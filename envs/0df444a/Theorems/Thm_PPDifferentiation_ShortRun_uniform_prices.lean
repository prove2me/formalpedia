-- Prove2me | Theorems.Thm_PPDifferentiation_ShortRun_uniform_prices
-- name    : PPDifferentiation.ShortRun.uniform_prices
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T12:59:05.081086+00:00
-- url     : https://prove2.me/theorems/e76b719b-e741-45fb-bdd5-a856eb81b1ab
-- title:
--   §4 Stage 3 — equilibrium uniform prices and gross profits
-- statement:
--   Let $t>0$ and $x_A\le x_B$ be firm positions, with $-2<x_A+x_B<4$. When neither firm uses personalized pricing, simultaneous uniform pricing has a price Nash equilibrium at
--
--   $$p_A=\frac{t(x_B-x_A)(2+x_A+x_B)}3,\qquad p_B=\frac{t(x_B-x_A)(4-x_A-x_B)}3.$$
--
--   The resulting gross profits are $t(x_B-x_A)(2+x_A+x_B)^2/18$ for A and $t(x_B-x_A)(4-x_A-x_B)^2/18$ for B. These formulas supply the benchmark pricing subgame.
--
--   **Formalization Note** The order $x_A\le x_B$ is the page's own normalization. The sum bounds $-2<x_A+x_B<4$ are added: they keep the indifferent consumer inside $[0,1]$, where the displayed interior-price formula applies. At $x_A=x_B$ both prices and profits are $0$ (Bertrand with ties split equally).
-- source:
--   Li, Wang, Nault, Is Personalized Pricing Profitable When Firms Can Differentiate?, working paper, SSRN abstract 3881900 (version of August 3, 2021), §4, pp. 8–9, Stage 3

import Mathlib
import Definitions.Def_PPDifferentiation_ShortRun_Setting

namespace PPDifferentiation.ShortRun

theorem uniform_prices (t xA xB : ℝ) (ht : 0 < t)
    (hord : xA ≤ xB) (hlo : -2 < xA + xB) (hhi : xA + xB < 4) :
    let pA := t * (xB - xA) * (2 + xA + xB) / 3
    let pB := t * (xB - xA) * (4 - xA - xB) / 3
    PPDifferentiation.Costless.IsPriceNE t xA xB pA pB ∧
    PPDifferentiation.Costless.uProf t xA xB pA pB = t * (xB - xA) * (2 + xA + xB)^2 / 18 ∧
    PPDifferentiation.Costless.uProf t xB xA pB pA = t * (xB - xA) * (4 - xA - xB)^2 / 18 := by sorry

end PPDifferentiation.ShortRun
