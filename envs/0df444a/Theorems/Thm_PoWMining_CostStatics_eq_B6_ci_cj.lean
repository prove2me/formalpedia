-- Prove2me | Theorems.Thm_PoWMining_CostStatics_eq_B6_ci_cj
-- name    : PoWMining.CostStatics.eq_B6_ci_cj
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:03.422263+00:00
-- url     : https://prove2.me/theorems/cfe212ec-8312-47d5-94e8-495238e4bd65
-- title:
--   (B.6), p. 42, first two lines — the share h*ᵢ/H* decreases in cᵢ and increases in cⱼ, in closed form
-- statement:
--   Under the standing assumptions ($n \ge 2$, $R > 0$, $\gamma \ge 0$, all $c_k > 0$, all $n$ miners active), let $g = H^*$ be the aggregate equilibrium hash rate, $f_i = h^*_i$ the equilibrium hash rate of miner $i$ and $c^{(n)} = c_1 + \dots + c_n$. Then for every other miner $j \ne i$ the hash rate share $h^*_i/H^*$ is differentiable in $c_i$ and in $c_j$, with
--   $$\frac{\partial}{\partial c_i}\frac{h^*_i}{H^*} = -\frac{g}{R + \gamma g^2}\Big(1 - \frac{c_i + 2\gamma f_i}{c^{(n)} + 2\gamma g}\Big) < 0,$$
--   $$\frac{\partial}{\partial c_j}\frac{h^*_i}{H^*} = \frac{g}{R + \gamma g^2}\,\frac{c_i + 2\gamma f_i}{c^{(n)} + 2\gamma g} > 0.$$
--
--   A miner's share falls when its own cost rises and rises when a competitor's cost rises, whatever the size of the share.
--
--   **Formalization Note.** Derivatives are one-variable derivatives along `Function.update`, stated with `HasDerivAt`. Miner indices are 0-based.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 42, (B.6), first two lines

import Mathlib
import Definitions.Def_PoWMining_CostStatics_Setting

namespace PoWMining.CostStatics

theorem eq_B6_ci_cj {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i j : Fin n)
    (hij : i ≠ j) :
    HasDerivAt (fun t => share (Function.update c i t) γ R i)
      (-(gH c γ R) / (R + γ * gH c γ R ^ 2)
        * (1 - (c i + 2 * γ * hstar c γ R i) / (cumCost c + 2 * γ * gH c γ R))) (c i) ∧
    -(gH c γ R) / (R + γ * gH c γ R ^ 2)
        * (1 - (c i + 2 * γ * hstar c γ R i) / (cumCost c + 2 * γ * gH c γ R)) < 0 ∧
    HasDerivAt (fun t => share (Function.update c j t) γ R i)
      (gH c γ R / (R + γ * gH c γ R ^ 2)
        * ((c i + 2 * γ * hstar c γ R i) / (cumCost c + 2 * γ * gH c γ R))) (c j) ∧
    0 < gH c γ R / (R + γ * gH c γ R ^ 2)
        * ((c i + 2 * γ * hstar c γ R i) / (cumCost c + 2 * γ * gH c γ R)) := by sorry

end PoWMining.CostStatics
