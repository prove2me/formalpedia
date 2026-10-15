-- Prove2me | Theorems.Thm_PoWMining_CapacityStatics_hstar_derivatives
-- name    : PoWMining.CapacityStatics.hstar_derivatives
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:27.004014+00:00
-- url     : https://prove2.me/theorems/03da6f2c-8325-4ee8-bbe4-1ce939eef891
-- title:
--   (B.4) γ- and R-lines, pp. 40–41 — closed forms of ∂h*ᵢ/∂γ = Δ⁽ᵞ⁾ᵢ,₁ + Δ⁽ᵞ⁾ᵢ,₂ and ∂h*ᵢ/∂R = Δ⁽ᴿ⁾ᵢ,₁ + Δ⁽ᴿ⁾ᵢ,₂
-- statement:
--   Under the standing assumptions of Proposition 4.8 ($n\ge2$, $R>0$, $\gamma>0$, positive sorted costs, all $n$ miners active), write $c^{(n)}=c_1+\dots+c_n$, $g = g(c,\gamma,R)$ for the aggregate hash rate of (B.3) and $f_i = h^*_i = f_i(c,\gamma,R;g)$ for the equilibrium hash rate of active miner $i$. Then $h^*_i$ is differentiable in $\gamma$ and in $R$, and
--   $$\frac{\partial h^*_i}{\partial\gamma} = \Delta^{(\gamma)}_{i,1}+\Delta^{(\gamma)}_{i,2} = -\frac{f_i g^2}{R+\gamma g^2}\left(1 + \frac{g}{f_i}\,\frac{\frac{R}{g} - 2(c_i+\gamma f_i)}{c^{(n)}+2\gamma g}\right),$$
--   $$\frac{\partial h^*_i}{\partial R} = \Delta^{(R)}_{i,1}+\Delta^{(R)}_{i,2} = \frac{g^2(c_i+\gamma f_i)}{R(R+\gamma g^2)}\left(1 + \frac{\frac{R}{g} - 2(c_i+\gamma f_i)}{c_i+\gamma f_i}\,\frac{c^{(n)}+\gamma g}{c^{(n)}+2\gamma g}\right),$$
--   where $\Delta^{(\gamma)}_{i,1}=\partial f_i/\partial\gamma$, $\Delta^{(\gamma)}_{i,2}=(\partial f_i/\partial g)(\partial g/\partial\gamma)$, and likewise for $R$.
--
--   These closed forms are the explicit expressions behind Proposition 4.8: they show the direct/indirect decomposition is the total derivative, and the $R$-line is the one whose positivity is the first claim of the proposition's second row.
--
--   **Formalization Note** Miners are `Fin n`, 0-based. The $\Delta$'s are the derivative-defined quantities of the definition `Sensitivities`; the statement asserts both that the total derivative of $h^*_i$ has the displayed value and that the sum of the derivative-defined $\Delta$'s equals it. Division by $f_i$ and by $c_i+\gamma f_i$ is legitimate since both are positive under activity.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, pp. 40–41, proof of Propositions 4.6 and 4.8, (B.4), third and fourth lines

import Mathlib
import Definitions.Def_PoWMining_CapacityStatics_ClosedForms
import Definitions.Def_PoWMining_CapacityStatics_Sensitivities

namespace PoWMining.CapacityStatics
theorem hstar_derivatives {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i : Fin n) :
    let C := PoWMining.CostStatics.cumCost c
    let g := PoWMining.CostStatics.gH c γ R
    let f := PoWMining.CostStatics.hstar c γ R i
    HasDerivAt (fun x => PoWMining.CostStatics.hstar c x R i)
        (-(f * g ^ 2 / (R + γ * g ^ 2)) *
          (1 + g / f * ((R / g - 2 * (c i + γ * f)) / (C + 2 * γ * g)))) γ ∧
      DeltaG1 c γ R i + DeltaG2 c γ R i =
        -(f * g ^ 2 / (R + γ * g ^ 2)) *
          (1 + g / f * ((R / g - 2 * (c i + γ * f)) / (C + 2 * γ * g))) ∧
    HasDerivAt (fun x => PoWMining.CostStatics.hstar c γ x i)
        (g ^ 2 * (c i + γ * f) / (R * (R + γ * g ^ 2)) *
          (1 + (R / g - 2 * (c i + γ * f)) / (c i + γ * f) * ((C + γ * g) / (C + 2 * γ * g)))) R ∧
      DeltaR1 c γ R i + DeltaR2 c γ R i =
        g ^ 2 * (c i + γ * f) / (R * (R + γ * g ^ 2)) *
          (1 + (R / g - 2 * (c i + γ * f)) / (c i + γ * f) * ((C + γ * g) / (C + 2 * γ * g))) := by sorry
end PoWMining.CapacityStatics
