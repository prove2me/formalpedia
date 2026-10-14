-- Prove2me | Theorems.Thm_RoundRobinEq_CancelableBluff_fact_3_1
-- name    : RoundRobinEq.CancelableBluff.fact_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:19.137779+00:00
-- url     : https://prove2.me/theorems/7d949de0-c825-4395-80e1-3f98916c438e
-- title:
--   Fact 3.1 — Round-Robin on the bluff profile returns the truthful allocation
-- statement:
--   Let $\boldsymbol\succ^*$ be a strict variant of the truthful profile for valuations $v_1, \dots, v_n$, and let $\boldsymbol\succ^{\mathrm b}$ be the corresponding bluff profile, in which every agent reports $h_1 \succ h_2 \succ \cdots \succ h_m$, the order in which Round-Robin$(\boldsymbol\succ^*)$ allocated the goods. Then
--   $$
--   \text{Round-Robin}(\boldsymbol\succ^{\mathrm b}) = \text{Round-Robin}(\boldsymbol\succ^*),
--   $$
--   that is, every agent receives the same bundle under both profiles.
--
--   Together with Proposition 2.5 and Theorem 3.2 this shows that Round-Robin with cancelable valuations has an exact pure Nash equilibrium whose allocation is EF1.
--
--   **Formalization Note** The equality is of the bundle functions `Fin n → Finset M`. The valuations enter only through `IsStrictTruthful`; no property of them (and not the standing $m = kn$) is needed for this fact, so none is assumed.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, p. 8, Fact 3.1

import Mathlib
import Definitions.Def_RoundRobinEq_CancelableBluff_Setting

namespace RoundRobinEq.CancelableBluff

theorem fact_3_1 {n : ℕ} [NeZero n] {M : Type*} [Fintype M] [DecidableEq M]
    (v : Fin n → Finset M → ℝ) (σ : Fin n → List M) (hσ : IsStrictTruthful v σ) :
    roundRobin (bluff σ) = roundRobin σ := by sorry

end RoundRobinEq.CancelableBluff
