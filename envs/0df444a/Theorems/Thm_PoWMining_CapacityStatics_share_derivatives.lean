-- Prove2me | Theorems.Thm_PoWMining_CapacityStatics_share_derivatives
-- name    : PoWMining.CapacityStatics.share_derivatives
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:31.605463+00:00
-- url     : https://prove2.me/theorems/c63f5836-df43-4c6e-9a15-86dddadb9807
-- title:
--   (B.6) γ- and R-lines, pp. 42–43 — closed forms of ∂(h*ᵢ/H*)/∂γ and ∂(h*ᵢ/H*)/∂R, with their p. 43 rewrites
-- statement:
--   Under the standing assumptions of Proposition 4.8 ($n\ge2$, $R>0$, $\gamma>0$, positive sorted costs, all $n$ miners active), write $c^{(n)}=c_1+\dots+c_n$, $g = H^*$ for the aggregate hash rate of (B.3) and $f_i = h^*_i$ for the equilibrium hash rate of active miner $i$. The hash rate share $h^*_i/H^*$ is differentiable in $\gamma$ and in $R$, with
--   $$\frac{\partial}{\partial\gamma}\frac{h^*_i}{H^*} = -\frac{1}{R+\gamma g^2}\left(f_i g - \frac{g^2}{c^{(n)}+2\gamma g}(c_i+2\gamma f_i)\right) = -\frac{1}{R+\gamma g^2}\left(f_i\Big(g - \frac{\gamma g^2}{c^{(n)}+2\gamma g}\Big) - \frac{g^2}{c^{(n)}+2\gamma g}(c_i+\gamma f_i)\right),$$
--   $$\frac{\partial}{\partial R}\frac{h^*_i}{H^*} = \frac{1}{R+\gamma g^2}\left(\frac{g}{R}(c_i+\gamma f_i) - (n-1)\frac{c_i+2\gamma f_i}{c^{(n)}+2\gamma g}\right) = \frac{1}{R+\gamma g^2}\left((c_i+\gamma f_i)\Big(\frac{g}{R} - \frac{n-1}{c^{(n)}+2\gamma g}\Big) - (n-1)\frac{\gamma f_i}{c^{(n)}+2\gamma g}\right).$$
--
--   The first form of each line is (B.6); the second is the rewrite on p. 43, in which the dependence on $i$ enters only through $f_i$ and $c_i+\gamma f_i$. This is what makes the monotonicity in $i$ of Proposition 4.8 visible.
--
--   **Formalization Note** Miners are `Fin n`, 0-based. The share is $f_i/g$ with $g>0$ under the standing assumptions, so no division by zero occurs.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, pp. 42–43, proof of Propositions 4.6 and 4.8, (B.6), third and fourth lines, and the final lines of the two computations on p. 43

import Mathlib
import Definitions.Def_PoWMining_CapacityStatics_ClosedForms

namespace PoWMining.CapacityStatics
theorem share_derivatives {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i : Fin n) :
    let C := PoWMining.CostStatics.cumCost c
    let g := PoWMining.CostStatics.gH c γ R
    let f := PoWMining.CostStatics.hstar c γ R i
    HasDerivAt (fun x => PoWMining.CostStatics.share c x R i)
        (-(1 / (R + γ * g ^ 2)) * (f * g - g ^ 2 / (C + 2 * γ * g) * (c i + 2 * γ * f))) γ ∧
      -(1 / (R + γ * g ^ 2)) * (f * g - g ^ 2 / (C + 2 * γ * g) * (c i + 2 * γ * f)) =
        -(1 / (R + γ * g ^ 2)) *
          (f * (g - γ * g ^ 2 / (C + 2 * γ * g)) - g ^ 2 / (C + 2 * γ * g) * (c i + γ * f)) ∧
    HasDerivAt (fun x => PoWMining.CostStatics.share c γ x i)
        (1 / (R + γ * g ^ 2) *
          (g / R * (c i + γ * f) - ((n : ℝ) - 1) * ((c i + 2 * γ * f) / (C + 2 * γ * g)))) R ∧
      1 / (R + γ * g ^ 2) *
          (g / R * (c i + γ * f) - ((n : ℝ) - 1) * ((c i + 2 * γ * f) / (C + 2 * γ * g))) =
        1 / (R + γ * g ^ 2) *
          ((c i + γ * f) * (g / R - ((n : ℝ) - 1) / (C + 2 * γ * g)) -
            ((n : ℝ) - 1) * (γ * f / (C + 2 * γ * g))) := by sorry
end PoWMining.CapacityStatics
