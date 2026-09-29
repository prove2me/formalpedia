-- Prove2me | Theorems.Thm_StochasticProg_IntegerLShaped_prop4_integer_lshaped_finite_convergence
-- name    : StochasticProg.IntegerLShaped.prop4_integer_lshaped_finite_convergence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T20:13:50.628989+00:00
-- url     : https://prove2.me/theorems/87bb3d92-e249-4013-9214-ada75c232709
-- title:
--   Chapter 7, Proposition 4 — finite convergence of the Integer L-shaped method
-- statement:
--   Let `d` be a stochastic integer program with binary first-stage variables and
--   relatively complete recourse (every first-stage-feasible $x$ is second-stage feasible),
--   and let $L$ satisfy Assumption 2 (a finite lower bound on $Q(x)$ over the first-stage
--   feasible region).
--
--   **Chapter 7, Proposition 4.** Under Assumption 2, the Integer L-shaped method yields an
--   optimal solution of the SIP with relatively complete recourse and first-stage binary
--   variables (when one exists) in a finite number of steps.
--
--   Formally: there is a finite run of the algorithm's cut-adding transition (`Step`),
--   starting from no cuts and of length $N$ bounded by $2^{n_1}$ (the number of possible
--   first-stage binary solutions), reaching a state admitting no further transition; at that
--   terminal state, either no binary first-stage-feasible point exists at all, or some
--   binary first-stage-feasible $x$ is optimal for the terminal master problem *and*
--   minimizes the true deterministic-equivalent objective $c^{\mathsf T}x + Q(x)$ over every
--   binary first-stage-feasible point — i.e. $x$ solves the SIP.
--
--   **Formalization Note** The bound $N \le 2^{n_1}$ formalizes the proof's "there are at
--   most $2^{n_1}$ different first-stage solutions": every application of the algorithm's
--   Step 6 either fathoms the current binary solution or excludes it from ever recurring as
--   the master's optimum by recording a fresh cut, so the process cannot revisit the same
--   binary point twice. See `MODERATION_NOTES.md` for the scope note on abstracting away
--   the explicit branch-and-bound tree (Steps 0, 1, 3, 4).
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 293, Chapter 7, Proposition 4

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_IntegerLShaped_Instance
import Definitions.Def_StochasticProg_IntegerLShaped_Algorithm

namespace StochasticProg.IntegerLShaped

open StochasticProg.Recourse

variable {n1 n2 m1 m2 K : ℕ}

/-- Chapter 7, Proposition 4 (p. 293): "Under Assumption 2, the integer L-shaped
method yields an optimal solution of a (SIP) with relatively complete recourse and
first-stage binary variables (when one exists) in a finite number of steps."

`hL` is Assumption 2 (p. 291); `hrcr` is "relatively complete recourse" (Ch. 3, p.
138, `K2 ⊇ K1`, restated for the SIP's `Y`-restricted value in `RelativelyCompleteRecourse`).
The algorithm is the object quantified over via `Step`/`path`: starting from no cuts,
every run reaches, within `N` bounded by the finite total number of possible cut
subsets `Fintype.card (Finset (Fin n1)) = 2^n1` (the proof's "there are at most `2^n1`
different first-stage solutions"), a state `path N` admitting no further `Step`
transition. Termination is then either "no first-stage binary feasible solution
exists" (Step 1, "if none exists, stop") or a binary SIP-feasible point that is
`IsBBOptimal` for the final cut set *and* globally optimal against every binary
SIP-feasible point's true objective `objY` — the "optimal solution ... in a finite
number of steps" the proposition asserts. -/
theorem prop4_integer_lshaped_finite_convergence (d : Data n1 n2 m1 m2 K) (L : ℝ)
    (hL : ∀ x, x ∈ K1X d → Binary x → (L : EReal) ≤ QY d x)
    (hrcr : RelativelyCompleteRecourse d) :
    ∃ (N : ℕ) (qS : Finset (Fin n1) → ℝ) (path : ℕ → State n1),
      N ≤ Fintype.card (Finset (Fin n1)) ∧
      path 0 = ∅ ∧
      (∀ i, i < N → Step d L qS (path i) (path (i + 1))) ∧
      (∀ Cuts', ¬ Step d L qS (path N) Cuts') ∧
      ((∀ x, x ∈ K1X d → ¬ Binary x) ∨
        (∃ x θ, IsBBOptimal d (path N) L qS x θ ∧
          ∀ x', x' ∈ K1X d → Binary x' → objY d x ≤ objY d x')) := by sorry

end StochasticProg.IntegerLShaped
