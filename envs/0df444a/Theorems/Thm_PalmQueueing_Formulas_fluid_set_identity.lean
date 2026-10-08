-- Prove2me | Theorems.Thm_PalmQueueing_Formulas_fluid_set_identity
-- name    : PalmQueueing.Formulas.fluid_set_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T01:03:35.755249+00:00
-- url     : https://prove2.me/theorems/7bc9342d-ddcc-4f9f-80a5-2ea2101f6f3b
-- title:
--   Lemma 3.1.1 — the set identity behind the fluid Little formula
-- statement:
--   **Lemma 3.1.1.** Let $\{W(t)\}$ be the stationary workload in a stable single server
--   fluid queue. For all $s < t$, the following sets are equal:
--   $$ F = \{u \in [s,t] \;;\; W(u) > C_{u,t}\}, \qquad G = \{u \in [s,t] \;;\; W(t) > A_{u,t}\} . $$
--
--   The left description says "the work still in the buffer at $u$ exceeds everything the server could
--   drain between $u$ and $t$"; the right says "the work in the buffer at $t$ exceeds everything that
--   arrived since $u$". That these describe the same instants is what turns the fluid workload into an
--   integral over the arrival measure — Property 3.1.1 on the same page reads off
--   $$ W(t) = \int_{(-\infty,t]} \mathbf{1}_{W(s) > C_{s,t}} A(ds) \tag{3.1.39} $$
--   when $A$ is absolutely continuous — and that is the fluid analogue of Little's formula.
--
--   Both inclusions come from the fluid-queue representation (2.7.5) and nothing else. If $u \in F$
--   then $W(t) \ge W(u) + A_{u,t} - C_{u,t} > A_{u,t}$, so $u \in G$. Conversely if $u \in G$ then the
--   maximum in
--   $W(t) = \max(W(u) + A_{u,t} - C_{u,t}, \sup_{u \le v \le t}(A_{v,t} - C_{v,t}))$
--   cannot be achieved by the second term, since that term is bounded above by $A_{u,t}$; so
--   $W(u) + A_{u,t} - C_{u,t} = W(t) > A_{u,t}$, which implies $u \in F$.
--
--   **Formalization Note.** The framework of §2.7 is carried as hypotheses: $A$ and $C$ are the
--   interval functions of $\theta_t$-compatible non-negative random measures, and $\{W(t)\}$ is a
--   $\theta_t$-compatible solution of the fluid-queue equation (2.7.6). The identity is stated
--   pathwise, for every $\omega$, as the page's sets are.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 193, Lemma 3.1.1

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess
import Definitions.Def_PalmQueueing_Loynes_FluidQueue

/-!
# Lemma 3.1.1: the set identity behind the fluid Little formula (§3.1.3, p.193)
-/

namespace PalmQueueing.Formulas

open MeasureTheory
open PalmQueueing.Palm PalmQueueing.Loynes

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Lemma 3.1.1** (p.193). Let `{W(t)}` be the stationary workload in a stable single server
fluid queue. For all `s < t`, the following sets are equal:

`F = { u ∈ [s,t] : W(u) > C_{u,t} }`,   `G = { u ∈ [s,t] : W(t) > A_{u,t} }`.

The left description says "the work still in the buffer at `u` exceeds everything the server could
drain between `u` and `t`"; the right says "the work in the buffer at `t` exceeds everything that
arrived since `u`". That these describe the same instants is what turns the fluid workload into an
integral over the arrival measure — Property 3.1.1 on the same page reads it off as
`W(t) = ∫_{(-∞,t]} 1_{W(s) > C_{s,t}} A(ds)` (3.1.39) — and that is the fluid analogue of Little's
formula.

Both inclusions come from the fluid-queue representation (2.7.5) of §2.7. If `u ∈ F` then
`W(t) ≥ W(u) + A_{u,t} − C_{u,t} > A_{u,t}`. Conversely if `u ∈ G` then the maximum in
`W(t) = max(W(u) + A_{u,t} − C_{u,t}, sup_{u≤v≤t}(A_{v,t} − C_{v,t}))` cannot be achieved by the
second term, since that term is bounded above by `A_{u,t}`; so
`W(u) + A_{u,t} − C_{u,t} = W(t) > A_{u,t}`.

The framework and the notation for fluid queues are those of §2.7, Chapter 2, so `IsFluidWorkload`
is imported rather than restated: `A` and `C` are the interval functions of `θ_t`-compatible
non-negative random measures (`IsFlowMeasure`, p.128), and `{W(t)}` is a `θ_t`-compatible
solution of the fluid-queue equation `(2.7.6)`. The non-negativity of `A` is load-bearing: with
`C ≡ 0`, `A_{u,t} = −(t − u)` and `W ≡ 0`, which solves `(2.7.6)`, `F` is empty while `G = [s,t)`. -/
theorem fluid_set_identity (θ : Flow Ω) (A C : ℝ → ℝ → Ω → ℝ)
    (hA : IsFlowMeasure θ A) (hC : IsFlowMeasure θ C) (W : ℝ → Ω → ℝ)
    (hWcomp : IsCompatible θ W) (hW : IsFluidWorkload A C W) (s t : ℝ) (hst : s < t) (ω : Ω) :
    {u : ℝ | u ∈ Set.Icc s t ∧ C u t ω < W u ω}
      = {u : ℝ | u ∈ Set.Icc s t ∧ A u t ω < W t ω} := by sorry

end PalmQueueing.Formulas
