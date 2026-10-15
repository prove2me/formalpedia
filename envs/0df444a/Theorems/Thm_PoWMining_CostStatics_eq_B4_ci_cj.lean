-- Prove2me | Theorems.Thm_PoWMining_CostStatics_eq_B4_ci_cj
-- name    : PoWMining.CostStatics.eq_B4_ci_cj
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:57.004419+00:00
-- url     : https://prove2.me/theorems/afc6adff-6bf1-472c-aab3-4e626115c2eb
-- title:
--   (B.4), p. 40, first two lines — ∂h*ᵢ/∂cᵢ = Δᵢ,₁ + Δᵢ,₂ and ∂h*ᵢ/∂cⱼ = Δᵢ,₂ in closed form
-- statement:
--   Under the standing assumptions ($n \ge 2$, $R > 0$, $\gamma \ge 0$, all $c_k > 0$, all $n$ miners active), let $g$ be the aggregate equilibrium hash rate, $h^*_i = f_i$ the equilibrium hash rate of miner $i$ (B.3), $c^{(n)} = c_1 + \dots + c_n$, and let $\Delta_{i,1} = \partial f_i/\partial c_i$ (aggregate fixed) and $\Delta_{i,2} = (\partial f_i/\partial g)(\partial g/\partial c_i)$ be the direct and indirect sensitivities. Then for every other miner $j \ne i$:
--
--   1. $h^*_i$ is differentiable in $c_i$, with
--   $$\frac{\partial h^*_i}{\partial c_i} = \Delta_{i,1} + \Delta_{i,2} = -\frac{g^2}{R + \gamma g^2}\Big(1 + \frac{\frac Rg - 2(c_i + \gamma f_i)}{c^{(n)} + 2\gamma g}\Big);$$
--   2. $h^*_i$ is differentiable in $c_j$, with
--   $$\frac{\partial h^*_i}{\partial c_j} = \Delta_{i,2} = -\frac{g^2}{R + \gamma g^2}\,\frac{\frac Rg - 2(c_i + \gamma f_i)}{c^{(n)} + 2\gamma g}.$$
--
--   These closed forms are the explicit expressions behind Proposition 4.6.
--
--   **Formalization Note.** $\Delta_{i,1}$, $\Delta_{i,2}$ are defined by derivatives in `PoWMining.CostStatics.Setting`, not by these formulas. Derivatives are one-variable derivatives along `Function.update`, stated with `HasDerivAt`. Miner indices are 0-based (`Fin n`).
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 40, (B.4), first two lines

import Mathlib
import Definitions.Def_PoWMining_CostStatics_Setting

namespace PoWMining.CostStatics

theorem eq_B4_ci_cj {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i j : Fin n)
    (hij : i ≠ j) :
    HasDerivAt (fun t => hstar (Function.update c i t) γ R i)
      (Delta1 c γ R i + Delta2 c γ R i) (c i) ∧
    Delta1 c γ R i + Delta2 c γ R i
      = -(gH c γ R ^ 2) / (R + γ * gH c γ R ^ 2)
          * (1 + (R / gH c γ R - 2 * (c i + γ * hstar c γ R i))
                  / (cumCost c + 2 * γ * gH c γ R)) ∧
    HasDerivAt (fun t => hstar (Function.update c j t) γ R i) (Delta2 c γ R i) (c j) ∧
    Delta2 c γ R i
      = -(gH c γ R ^ 2) / (R + γ * gH c γ R ^ 2)
          * ((R / gH c γ R - 2 * (c i + γ * hstar c γ R i))
              / (cumCost c + 2 * γ * gH c γ R)) := by sorry

end PoWMining.CostStatics
