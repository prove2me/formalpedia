-- Prove2me | Theorems.Thm_ProcessingNetworks_Stability_empty_state_reachable
-- name    : ProcessingNetworks.Stability.empty_state_reachable
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:20:45.331809+00:00
-- url     : https://prove2.me/theorems/98c81c6b-efc3-4d26-ab2e-de303486def5
-- title:
--   Proposition 3.9 — reachability of the empty state
-- statement:
--   Let $\tau := \inf\{t > 0 : E(t) \ne E(0)\}$ be the time of the first external
--   arrival, so that $\{\tau > t\}$ is the event that no external arrival occurs in $(0, t]$,
--   i.e. $E(t) = E(0)$. Equation (3.18) of the book asks: for every state $x$, is there a time
--   $t > 0$ such that, conditional on no external arrivals up to $t$, the network is empty at $t$
--   with positive probability?
--   $$
--   \Pr_x\big(Z(t) = 0 \mid \tau > t\big) > 0 \quad \text{for some } t > 0. \tag{3.18}
--   $$
--
--   **Proposition 3.9.** Assume the empty state $x^\ast$ (Assumption 3.1's $f(x^\ast) = (0,0)$) is
--   unique. Under (3.18) and the baseline stochastic assumptions, $x^\ast$ is reachable from every
--   state $x \in \mathcal{X}$: there is a time $t > 0$ with $\Pr_x(X(t) = x^\ast) > 0$.
--
--   This is the book's practical sufficient condition for the irreducibility Assumption 3.1 itself
--   demands, letting a modeler check irreducibility via a single "the system can empty out" condition
--   rather than verifying full irreducibility directly.
--
--   **Formalization note.** The proof's first step (3.19), $\Pr_x\{X(t) = x^\ast\} = \Pr_x\{Z(t) = 0\}$,
--   uses Remark 3.3 of the book — no service can be open while all buffers are empty, $Z(t) = 0
--   \Rightarrow N(t) = 0$, a consequence of the Chapter 2 model — together with the uniqueness of the
--   empty state; Remark 3.3 is included as the explicit hypothesis `hZN`. The event $\{\tau > t\}$ is
--   written directly as $\{E_i(t) = E_i(0) \text{ for all } i\}$ (equivalent for a nondecreasing
--   counting process, and free of the junk value an infimum over an empty set would take when there
--   are no arrivals at all). $\Pr_x$ is the conditional measure `ℙ[|{ω | M.X 0 ω = x}]`, following the
--   book's own convention $P_x(A) = P(A \mid X(0) = x)$ (Definition D.2), with the hypothesis `hsupp`
--   that every state carries positive initial mass so that each $\Pr_x$ is defined.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 61, Proposition 3.9

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation

namespace ProcessingNetworks.Stability

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Proposition 3.9 (reachability of the empty state), Dai & Harrison, p. 61: assume the empty
state `x*` (`hxstar`) is unique among states mapping to `(0,0)` under `f`, and (Remark 3.3, a
consequence of the Chapter 2 model that the proof uses) that no service is open while all buffers
are empty: `Z(t) = 0 → N(t) = 0`. Under Eq. (3.18) — for every state `x` there is a time `t > 0`
with `P_x(Z(t) = 0 ∣ τ > t) > 0`, where `τ` is the time of the first external arrival, so that
`{τ > t}` is the event `E(t) = E(0)` of no external arrival in `(0, t]` — and the baseline
stochastic assumptions, `x*` is reachable from every state `x`: there is a time `t > 0` with
`P_x(X(t) = x*) > 0`. `P_x` is `ℙ[|{X(0) = x}]`; every state is given positive initial mass by
`hsupp`, so that these conditional laws are all defined. -/
theorem empty_state_reachable {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω]
    {I J : ℕ} {N0 : Fin J → ℕ} {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {E : Fin I → ℝ → Ω → ℕ} {lam : Fin I → ℝ≥0}
    {v : Fin J → ℕ → Ω → ℝ} {φ : Fin J → ℕ → Ω → Fin I → ℕ}
    {m : Fin J → ℝ} {Γ : Fin J → Fin I → ℝ} {Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)}
    (hbase : BaselineAssumptions I J N0 E lam v φ m Γ Psi)
    (M : MarkovRepresentation Xstate I J N Z)
    (hsupp : ∀ x : Xstate, ℙ {ω | M.X 0 ω = x} ≠ 0)
    (hZN : ∀ (t : ℝ) (ω : Ω), Z t ω = 0 → N t ω = 0)
    (xstar : Xstate) (hxstar : M.f xstar = (0, 0))
    (hxstar_unique : ∀ x, M.f x = (0, 0) → x = xstar)
    (h318 : ∀ x : Xstate, ∃ t : ℝ, 0 < t ∧
      (ℙ[|{ω | M.X 0 ω = x}])[|{ω | ∀ i, E i t ω = E i 0 ω}] {ω | Z t ω = 0} > 0) :
    ∀ x : Xstate, ∃ t : ℝ, 0 < t ∧ (ℙ[|{ω | M.X 0 ω = x}]) {ω | M.X t ω = xstar} > 0 := by sorry

end ProcessingNetworks.Stability
