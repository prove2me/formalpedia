-- Prove2me | Theorems.Thm_PPDifferentiation_Costless_uniform_prices
-- name    : PPDifferentiation.Costless.uniform_prices
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:26:09.022351+00:00
-- url     : https://prove2.me/theorems/3ce7db40-1116-447c-a192-e50c93c63833
-- title:
--   §4, pp. 8–9, Stage 3 — uniform prices t(x_B − x_A)(2 + x_A + x_B)/3 and t(x_B − x_A)(4 − x_A − x_B)/3 form an equilibrium, with profits /18
-- statement:
--   Let $t>0$, $x_A<x_B$ and $-2<x_A+x_B<4$. When neither firm implements personalized pricing and the firms choose uniform prices simultaneously, the prices
--   $$p_A=\frac{t(x_B-x_A)(2+x_A+x_B)}{3},\qquad p_B=\frac{t(x_B-x_A)(4-x_A-x_B)}{3}$$
--   form a price equilibrium, and the equilibrium profits are
--   $$\pi_A=\frac{t(x_B-x_A)(2+x_A+x_B)^2}{18},\qquad \pi_B=\frac{t(x_B-x_A)(4-x_A-x_B)^2}{18}.$$
--
--   This is the uniform-pricing cell of the stage-2 payoff matrix (Table 3) and the stage-3 outcome of the paper's uniform pricing benchmark.
--
--   **Formalization Note** The range $-2<x_A+x_B<4$ and the strict order $x_A<x_B$ are added: they keep the indifferent consumer $(2+x_A+x_B)/6$ inside $(0,1)$, where the page's first-order conditions apply. Each firm's deviation ranges over all real prices.
-- source:
--   Li, Wang, Nault, Is Personalized Pricing Profitable When Firms Can Differentiate?, working paper, SSRN abstract 3881900 (version of August 3, 2021), pp. 8–9, §4 Stage 3

import Mathlib
import Definitions.Def_PPDifferentiation_Costless_Setting

namespace PPDifferentiation.Costless

theorem uniform_prices (t : ℝ) (ht : 0 < t) (xA xB : ℝ) (hAB : xA < xB)
    (hlo : -2 < xA + xB) (hhi : xA + xB < 4) :
    IsPriceNE t xA xB (t * (xB - xA) * (2 + xA + xB) / 3) (t * (xB - xA) * (4 - xA - xB) / 3) ∧
    uProf t xA xB (t * (xB - xA) * (2 + xA + xB) / 3) (t * (xB - xA) * (4 - xA - xB) / 3) =
      t * (xB - xA) * (2 + xA + xB)^2 / 18 ∧
    uProf t xB xA (t * (xB - xA) * (4 - xA - xB) / 3) (t * (xB - xA) * (2 + xA + xB) / 3) =
      t * (xB - xA) * (4 - xA - xB)^2 / 18 := by sorry

end PPDifferentiation.Costless
