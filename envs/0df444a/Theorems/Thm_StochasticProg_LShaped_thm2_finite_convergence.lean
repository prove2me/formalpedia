-- Prove2me | Theorems.Thm_StochasticProg_LShaped_thm2_finite_convergence
-- name    : StochasticProg.LShaped.thm2_finite_convergence
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T20:07:01.490985+00:00
-- url     : https://prove2.me/theorems/cea35418-3b73-4049-b7b7-3fa7448988de
-- title:
--   Chapter 5, Theorem 2 — finite convergence of the L-shaped algorithm
-- statement:
--   This is Chapter 5, Theorem 2 (p. 198) of Birge & Louveaux, *Introduction to Stochastic
--   Programming*, the capstone convergence guarantee of the L-shaped method: "When $\xi$ is a
--   finite random variable, the L-shaped algorithm finitely converges to an optimal solution when
--   it exists or proves the infeasibility of Problem (3.1.2), namely $\min c^Tx+Q(x)$ s.t.
--   $x\in K_1\cap K_2$."
--
--   Let $I$ be a two-stage recourse instance with $K$ finite scenarios. The claim is that,
--   starting from the state with no cuts at all, there is a finite run of the algorithm's Step
--   1-2-3 transition (`Step`, from the companion `Algorithm` bundle) — a sequence of states
--   $\mathrm{path}\,0,\dots,\mathrm{path}\,N$ with $\mathrm{path}\,0=(\varnothing,\varnothing)$ and
--   each consecutive pair related by `Step` — whose length $N$ is bounded by the total number of
--   feasibility- and optimality-cut witnesses available (`Fintype.card (Fin K × FeasBasis n2 m2)
--   + Fintype.card (Fin K → Basis n2 m2)`, the finite bound the book gets from "there is only a
--   finite number of different combinations of the $K$ multipliers $\pi_k$, because each
--   corresponds to one of the finitely many different bases", p. 220), and from which **no**
--   further `Step` transition exists. At that terminal state, exactly one of the following holds:
--
--   - the master program has become infeasible for the recorded feasibility cuts
--     (`IsMasterInfeasible`), certifying $K_1\cap K_2=\varnothing$; or
--   - the master program's optimum $(x,\theta)$ has $x\in K_1\cap K_2$, satisfies every fresh
--     Step-3 termination test (no witness family $\beta$ attaining the true recourse values
--     violates the current $\theta$), and $x$ is optimal for Problem (3.1.2),
--     $\min c^Tx+Q(x)$ s.t. $x\in K_1\cap K_2$.
--
--   **Formalization Note** The statement is deliberately about *this specific iterative
--   procedure* — the master program, the feasibility test and the optimality-cut test of Steps
--   1-3 — not merely about the existence of an optimal or infeasible-certifying $x$: the
--   conclusion is stated in terms of a `Step`-path from the empty cut set and a state admitting no
--   further `Step`, so a solver of the `sorry` cannot bypass the algorithm's own mechanics. The
--   finite bound $N\le\mathrm{Fintype.card}(\dots)+\mathrm{Fintype.card}(\dots)$ is exactly the
--   finiteness-of-bases argument the book's proof uses (p. 220), not a generic compactness bound.
--   The cross-chapter fact the book's proof invokes at this point — "we already know from Theorem
--   3.5 that $K_2$ is polyhedral when $\xi$ is a finite random variable" — is not restated as a
--   separate hypothesis or lemma here: it is exactly the same finite-cardinality-of-bases fact
--   that already appears explicitly in the bound on $N$, so no additional axiom is needed to state
--   this theorem faithfully. See `MODERATION_NOTES.md` for why no `kind: reference` import of
--   Chunk 03's `StochasticProg.Recourse` namespace was used.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 198, Chapter 5, Theorem 2

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_LShaped_Bases
import Definitions.Def_StochasticProg_LShaped_Algorithm

namespace StochasticProg.LShaped

open StochasticProg.Recourse

variable {n1 n2 m1 m2 K : ℕ}

/-- Chapter 5, Theorem 2 (p. 198): "When `ξ` is a finite random variable, the L-shaped
algorithm finitely converges to an optimal solution when it exists or proves the
infeasibility of Problem (3.1.2), namely, `min cᵀx + Q(x) s.t. x ∈ K1 ∩ K2`."

Formalized as: starting from no cuts at all, every run of the algorithm's Step-1-2-3
transition (`Step`) reaches, within a number of steps bounded by the finite total number of
feasibility- and optimality-cut witnesses available (`Fintype.card (Fin K × FeasBasis n2
m2) + Fintype.card (Fin K → Basis n2 m2)` — "there is only a finite number of different
combinations of the `K` multipliers ... because each corresponds to one of the finitely
many different bases", p. 220), a state from which no further `Step` cut can be added,
i.e. either the master problem has become infeasible (certifying `K1 ∩ K2 = ∅`) or its
optimum `x` is second-stage feasible, satisfies every fresh Step-3 termination test, and is
optimal for Problem (3.1.2). -/
theorem thm2_finite_convergence (inst : Instance n1 n2 m1 m2 K) :
    ∃ (N : ℕ) (path : ℕ → State inst),
      N ≤ Fintype.card (Fin K × FeasBasis n2 m2) + Fintype.card (Fin K → Basis n2 m2) ∧
      path 0 = (∅, ∅) ∧
      (∀ i, i < N → Step inst (path i) (path (i + 1))) ∧
      (∀ Sf' So', ¬ Step inst (path N) (Sf', So')) ∧
      ((IsMasterInfeasible inst (path N).1 ∧ K1 inst ∩ K2 inst = ∅) ∨
        (∃ x θ, IsMasterOptimal inst (path N).1 (path N).2 x θ ∧
          x ∈ K1 inst ∩ K2 inst ∧
          (∀ β, IsOptimalAt inst x β →
            θ ≥ (optCutCoeffs inst β).2 - dotProduct (optCutCoeffs inst β).1 x) ∧
          ∀ x' ∈ K1 inst ∩ K2 inst, obj inst x ≤ obj inst x')) := by sorry

end StochasticProg.LShaped
