-- Prove2me | Theorems.Thm_RoundRobinEq_CancelableBluff_theorem_3_2
-- name    : RoundRobinEq.CancelableBluff.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:28:35.004686+00:00
-- url     : https://prove2.me/theorems/bc9249af-c47a-4c48-b154-817202f11471
-- title:
--   Theorem 3.2 — for cancelable valuations the bluff profile is an exact pure Nash equilibrium of Round-Robin
-- statement:
--   Let $n \ge 1$ agents share $m = kn$ indivisible goods, and let every agent's valuation $v_i$ be a cancelable valuation function (normalized and non-decreasing). Let $\boldsymbol\succ^*$ be any strict variant of the truthful profile (each agent ranks the goods by non-increasing singleton value $v_i(\{g\})$, ties broken in any fixed way), let $h_1, \dots, h_m$ be the goods in the order in which Round-Robin$(\boldsymbol\succ^*)$ allocates them, and let $\boldsymbol\succ^{\mathrm b} = (\succ^{\mathrm b}, \dots, \succ^{\mathrm b})$ be the bluff profile, where every agent reports $h_1 \succ^{\mathrm b} \cdots \succ^{\mathrm b} h_m$.
--
--   Then $\boldsymbol\succ^{\mathrm b}$ is an exact pure Nash equilibrium of Round-Robin: for every agent $i$ and every ranking $\succ_i'$ of $M$,
--   $$
--   v_i\big(A_i(\succ_i', \boldsymbol\succ^{\mathrm b}_{-i})\big) \le v_i\big(A_i(\boldsymbol\succ^{\mathrm b})\big),
--   $$
--   where $A_i(\cdot)$ is agent $i$'s bundle in the allocation Round-Robin returns.
--
--   The result generalizes the known existence of exact equilibria of Round-Robin for additive valuations to the strictly larger class of cancelable valuations, with an explicit equilibrium that can be computed by running Round-Robin once on truthful reports.
--
--   **Formalization Note** The conclusion is `IsApproxPNE 1 v (bluff σ)`: the bluff reports are rankings, and no deviation to any ranking `τ` raises the deviator's true value. The standing simplification $m = kn$ (p. 7) is carried as the hypothesis `hm`; the reduction of general $m$ by dummy goods is not formalized. The strict truthful profile `σ` is universally quantified, so the theorem holds for every tie-breaking, as on the page.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, p. 8, Theorem 3.2 (proof pp. 8–9)

import Mathlib
import Definitions.Def_RoundRobinEq_CancelableBluff_Setting

namespace RoundRobinEq.CancelableBluff

theorem theorem_3_2 {n : ℕ} [NeZero n] {M : Type*} [Fintype M] [DecidableEq M]
    (k : ℕ) (hm : Fintype.card M = k * n) (v : Fin n → Finset M → ℝ)
    (hv : ∀ i, IsValuation (v i)) (hc : ∀ i, IsCancelable (v i))
    (σ : Fin n → List M) (hσ : IsStrictTruthful v σ) :
    IsApproxPNE 1 v (bluff σ) := by sorry

end RoundRobinEq.CancelableBluff
