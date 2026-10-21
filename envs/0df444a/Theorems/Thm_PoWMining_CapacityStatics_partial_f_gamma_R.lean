-- Prove2me | Theorems.Thm_PoWMining_CapacityStatics_partial_f_gamma_R
-- name    : PoWMining.CapacityStatics.partial_f_gamma_R
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:46.266981+00:00
-- url     : https://prove2.me/theorems/c587fe32-4501-4ea3-8a41-1fd9c90b76a4
-- title:
--   p. 40, proof of Propositions 4.6 and 4.8 — ∂fᵢ/∂γ = −g³(R − cᵢg)/(R + γg²)² < 0 and ∂fᵢ/∂R = g²(cᵢ + γg)/(R + γg²)² > 0
-- statement:
--   Under the standing assumptions of Proposition 4.8 ($n\ge2$, $R>0$, $\gamma>0$, positive sorted costs, all $n$ miners active), let $g = g(c,\gamma,R)$ be the aggregate hash rate of (B.3) and $f_i(c,\gamma,R;G) = G(R-c_iG)/(R+\gamma G^2)$. With the aggregate argument held fixed at $G = g$, the map $f_i$ is differentiable in $\gamma$ and in $R$, and for every active miner $i$
--   $$\frac{\partial f_i}{\partial\gamma} = -g^3\,\frac{R - c_i g}{(R+\gamma g^2)^2} < 0, \qquad \frac{\partial f_i}{\partial R} = g^2\,\frac{c_i + \gamma g}{(R+\gamma g^2)^2} > 0.$$
--
--   These are the direct sensitivities $\Delta^{(\gamma)}_{i,1}$ and $\Delta^{(R)}_{i,1}$ of (B.4), and they give two of the four signs in Proposition 4.8.
--
--   **Formalization Note** Miners are `Fin n`, 0-based. The sign of $\partial f_i/\partial\gamma$ uses activity, $R - c_ig > 0$. The $c_i$- and $g$-derivatives of $f_i$ on the same display are posed in mission 2 of this series.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 40, proof of Propositions 4.6 and 4.8, display after 'To show (B.4), first note that simple calculations give'

import Mathlib
import Definitions.Def_PoWMining_CapacityStatics_ClosedForms

namespace PoWMining.CapacityStatics
theorem partial_f_gamma_R {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i : Fin n) :
    let g := PoWMining.CostStatics.gH c γ R
    HasDerivAt (fun x => PoWMining.CostStatics.fH c x R g i) (-(g ^ 3 * ((R - c i * g) / (R + γ * g ^ 2) ^ 2))) γ ∧
      -(g ^ 3 * ((R - c i * g) / (R + γ * g ^ 2) ^ 2)) < 0 ∧
    HasDerivAt (fun x => PoWMining.CostStatics.fH c γ x g i) (g ^ 2 * ((c i + γ * g) / (R + γ * g ^ 2) ^ 2)) R ∧
      0 < g ^ 2 * ((c i + γ * g) / (R + γ * g ^ 2) ^ 2) := by sorry
end PoWMining.CapacityStatics
