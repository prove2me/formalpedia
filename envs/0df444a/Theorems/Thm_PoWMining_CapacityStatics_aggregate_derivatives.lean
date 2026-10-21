-- Prove2me | Theorems.Thm_PoWMining_CapacityStatics_aggregate_derivatives
-- name    : PoWMining.CapacityStatics.aggregate_derivatives
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:28.399506+00:00
-- url     : https://prove2.me/theorems/982f2cbc-2649-45af-9ee4-5e0aa34778bc
-- title:
--   (B.2), p. 39 — ∂H*/∂γ = −(H*)²/(c⁽ⁿ⁾ + 2γH*) < 0 and ∂H*/∂R = (n − 1)/(c⁽ⁿ⁾ + 2γH*) > 0
-- statement:
--   Let $n$ active miners have costs $c_1\le\dots\le c_n$, all positive, with $n\ge2$, reward $R>0$, capacity parameter $\gamma>0$, and all miners active ($R-c_kg>0$). Write $c^{(n)} = c_1+\dots+c_n$, $H^* = g(c,\gamma,R)$ for the aggregate hash rate of (B.3), and $S = \sqrt{(c^{(n)})^2 + 4(n-1)R\gamma}$. Then $H^*$ is differentiable in $\gamma$ and in $R$, with
--   $$\frac{\partial H^*}{\partial\gamma} = -\frac{(c^{(n)})^2 + 2(n-1)R\gamma - c^{(n)}S}{2\gamma^2 S} = -\frac{(H^*)^2}{c^{(n)} + 2\gamma H^*} < 0,$$
--   $$\frac{\partial H^*}{\partial R} = \frac{n-1}{S} = \frac{n-1}{c^{(n)} + 2\gamma H^*} > 0.$$
--
--   A tighter capacity constraint lowers the aggregate hash rate and a larger reward raises it. These derivatives are the factors $\partial g/\partial\gamma$ and $\partial g/\partial R$ of the indirect sensitivities in (B.4).
--
--   **Formalization Note** The standing assumptions (including sorting and activity, which these identities do not need) are those of the whole proof of Proposition 4.8. The $c_i$-line of (B.2) is posed in mission 2 of this series.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 39, proof of Propositions 4.6 and 4.8, (B.2), second and third lines

import Mathlib
import Definitions.Def_PoWMining_CapacityStatics_ClosedForms

namespace PoWMining.CapacityStatics
theorem aggregate_derivatives {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) :
    let C := PoWMining.CostStatics.cumCost c
    let g := PoWMining.CostStatics.gH c γ R
    let S := Real.sqrt (C ^ 2 + 4 * ((n : ℝ) - 1) * R * γ)
    HasDerivAt (fun x => PoWMining.CostStatics.gH c x R)
        (-((C ^ 2 + 2 * ((n : ℝ) - 1) * R * γ - C * S) / (2 * γ ^ 2 * S))) γ ∧
      -((C ^ 2 + 2 * ((n : ℝ) - 1) * R * γ - C * S) / (2 * γ ^ 2 * S)) = -(g ^ 2 / (C + 2 * γ * g)) ∧
      -(g ^ 2 / (C + 2 * γ * g)) < 0 ∧
    HasDerivAt (fun x => PoWMining.CostStatics.gH c γ x) (((n : ℝ) - 1) / S) R ∧
      ((n : ℝ) - 1) / S = ((n : ℝ) - 1) / (C + 2 * γ * g) ∧
      0 < ((n : ℝ) - 1) / (C + 2 * γ * g) := by sorry
end PoWMining.CapacityStatics
