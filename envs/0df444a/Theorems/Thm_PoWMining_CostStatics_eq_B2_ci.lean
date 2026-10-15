-- Prove2me | Theorems.Thm_PoWMining_CostStatics_eq_B2_ci
-- name    : PoWMining.CostStatics.eq_B2_ci
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:52.733697+00:00
-- url     : https://prove2.me/theorems/ceafe3ee-2be7-4496-a393-7bbd01f8b410
-- title:
--   (B.2), p. 39 — the aggregate hash rate decreases in each cost: ∂H*/∂cᵢ = −H*/(c^(n) + 2γH*) < 0
-- statement:
--   Let $n \ge 2$ miners with costs $c_k > 0$, capacity parameter $\gamma \ge 0$ and reward $R > 0$ all be active, and let $H^* = g$ be the aggregate equilibrium hash rate of (4.1), with cumulative cost $c^{(n)} = c_1 + \dots + c_n$. Then $H^*$ is differentiable in each cost $c_i$, and
--   $$\frac{\partial H^*}{\partial c_i} = -\frac{H^*}{c^{(n)} + 2\gamma H^*} < 0.$$
--   Moreover, when $\gamma > 0$,
--   $$\frac{1}{2\gamma}\Big(\frac{c^{(n)}}{\sqrt{(c^{(n)})^2 + 4(n-1)R\gamma}} - 1\Big) = -\frac{H^*}{c^{(n)} + 2\gamma H^*}.$$
--
--   This is the first line of (B.2): the aggregate effect through which every miner's cost feeds into every other miner's hash rate.
--
--   **Formalization Note.** The derivative is along the $i$-th coordinate (`Function.update c i t`), stated with `HasDerivAt`. The middle expression of (B.2) exists only for $\gamma > 0$ and is stated as a separate implication; the outer formula is stated for all $\gamma \ge 0$, where at $\gamma = 0$ it reads $-H^*/c^{(n)}$ with $H^* = (n-1)R/c^{(n)}$. "All miners active" ($R - c_k H^* > 0$) is part of the standing assumptions.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 39, (B.2), first line, proof of Propositions 4.6 and 4.8

import Mathlib
import Definitions.Def_PoWMining_CostStatics_Setting

namespace PoWMining.CostStatics

theorem eq_B2_ci {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i : Fin n) :
    HasDerivAt (fun t => gH (Function.update c i t) γ R)
      (-(gH c γ R) / (cumCost c + 2 * γ * gH c γ R)) (c i) ∧
    -(gH c γ R) / (cumCost c + 2 * γ * gH c γ R) < 0 ∧
    (0 < γ → 1 / (2 * γ) * (cumCost c / Real.sqrt (cumCost c ^ 2 + 4 * ((n : ℝ) - 1) * R * γ) - 1)
      = -(gH c γ R) / (cumCost c + 2 * γ * gH c γ R)) := by sorry

end PoWMining.CostStatics
