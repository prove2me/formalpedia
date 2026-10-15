-- Prove2me | Theorems.Thm_PoWMining_CostStatics_partials_f
-- name    : PoWMining.CostStatics.partials_f
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:00.313308+00:00
-- url     : https://prove2.me/theorems/72752dfa-f00c-429f-9088-cdae1f0fa586
-- title:
--   p. 40, proof of Proposition 4.6 — ∂fᵢ/∂cᵢ = −g²/(R + γg²) < 0 and ∂fᵢ/∂g = g/(R + γg²)(R/g − 2(cᵢ + γfᵢ))
-- statement:
--   Under the standing assumptions ($n \ge 2$, $R > 0$, $\gamma \ge 0$, all $c_k > 0$, all $n$ miners active), let $g$ be the aggregate equilibrium hash rate and consider $f_i(c_1,\dots,c_n,G) = G(R - c_i G)/(R + \gamma G^2)$ from (B.3), with $f_i = f_i(g)$.
--
--   1. With the aggregate held fixed at $G = g$, $f_i$ is differentiable in $c_i$ and
--   $$\frac{\partial f_i}{\partial c_i} = -\frac{g^2}{R + \gamma g^2} < 0.$$
--   2. $f_i$ is differentiable in $G$ at $G = g$, with
--   $$\frac{\partial f_i}{\partial g} = \frac{R - c_i g}{R + \gamma g^2} + g\,\frac{-c_iR - 2\gamma R g + \gamma c_i g^2}{(R + \gamma g^2)^2} = \frac{g}{R + \gamma g^2}\Big(\frac Rg - 2(c_i + \gamma f_i)\Big).$$
--
--   These are the two partial derivatives from which the direct and indirect sensitivities $\Delta_{i,1}$, $\Delta_{i,2}$ of (B.4) are built.
--
--   **Formalization Note.** Derivatives are stated with `HasDerivAt`, the first along `Function.update c i t` with $G = g$ fixed, the second in the free aggregate argument $G$ of $f_i$. The intermediate lines of the paper's chain are not stated; the first and last forms are. Miner indices are 0-based.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 40, proof of Propositions 4.6 and 4.8 (displays before (B.5))

import Mathlib
import Definitions.Def_PoWMining_CostStatics_Setting

namespace PoWMining.CostStatics

theorem partials_f {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i : Fin n) :
    HasDerivAt (fun t => fH (Function.update c i t) γ R (gH c γ R) i)
      (-(gH c γ R ^ 2) / (R + γ * gH c γ R ^ 2)) (c i) ∧
    -(gH c γ R ^ 2) / (R + γ * gH c γ R ^ 2) < 0 ∧
    HasDerivAt (fun G => fH c γ R G i)
      ((R - c i * gH c γ R) / (R + γ * gH c γ R ^ 2)
        + gH c γ R * (-(c i) * R - 2 * γ * R * gH c γ R + γ * c i * gH c γ R ^ 2)
          / (R + γ * gH c γ R ^ 2) ^ 2) (gH c γ R) ∧
    (R - c i * gH c γ R) / (R + γ * gH c γ R ^ 2)
        + gH c γ R * (-(c i) * R - 2 * γ * R * gH c γ R + γ * c i * gH c γ R ^ 2)
          / (R + γ * gH c γ R ^ 2) ^ 2
      = gH c γ R / (R + γ * gH c γ R ^ 2)
          * (R / gH c γ R - 2 * (c i + γ * hstar c γ R i)) := by sorry

end PoWMining.CostStatics
