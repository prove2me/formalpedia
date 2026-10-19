-- Prove2me | Theorems.Thm_PPDifferentiation_Costless_one_pp_profits
-- name    : PPDifferentiation.Costless.one_pp_profits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:26:00.105006+00:00
-- url     : https://prove2.me/theorems/06127e18-a0f1-4044-95d5-8cb746661bfc
-- title:
--   Appendix A, pp. 33–34 — one firm with PP: the uniform leader's unique optimal price and the profits of Table 3
-- statement:
--   Let $t>0$ and $x_A<x_B$. Suppose exactly one firm implements personalized pricing; the uniform-price firm sets its price first and the targeting firm then prices each consumer.
--
--   1. *Only $B$ implements PP* ($A$ leads). If $0<x_A+x_B<4$, the price
--   $$p_A=\frac{t(x_A+x_B)(x_B-x_A)}{2}$$
--   is an optimal leader price for $A$, it is the only one, and the resulting profits are
--   $$\pi^{L}_t(x_A,x_B;p_A)=\frac{t(x_B-x_A)(x_A+x_B)^2}{8},\qquad \pi^{F}_t(x_A,x_B;p_A)=\frac{t(x_B-x_A)(4-x_A-x_B)^2}{16}.$$
--   2. *Only $A$ implements PP* ($B$ leads). If $-2<x_A+x_B<2$, the price
--   $$p_B=\frac{t(x_B-x_A)(2-x_A-x_B)}{2}$$
--   is the unique optimal leader price for $B$, and the profits are
--   $$\pi^{F}_t(x_B,x_A;p_B)=\frac{t(x_B-x_A)(2+x_A+x_B)^2}{16},\qquad \pi^{L}_t(x_B,x_A;p_B)=\frac{t(x_B-x_A)(2-x_A-x_B)^2}{8},$$
--   the first being $A$'s and the second $B$'s.
--
--   These are the two asymmetric cells of the stage-2 payoff matrix (Table 3), used in Lemma 1.
--
--   **Formalization Note** The paper treats case 2 "symmetrically" and does not print $p_B$; the price stated is the mirror image of case 1. The ranges $0<x_A+x_B<4$ and $-2<x_A+x_B<2$ and the strict order $x_A<x_B$ are added: they keep the leader's market share interior and make its optimum unique. Optimality is over all real prices. Uniqueness of the leader's optimum is what makes the follower's profit well defined.
-- source:
--   Li, Wang, Nault, Is Personalized Pricing Profitable When Firms Can Differentiate?, working paper, SSRN abstract 3881900 (version of August 3, 2021), pp. 33–34, Appendix A, proof of Lemma 1 (only one firm implements PP; Table 3)

import Mathlib
import Definitions.Def_PPDifferentiation_Costless_Setting

namespace PPDifferentiation.Costless

theorem one_pp_profits (t : ℝ) (ht : 0 < t) (xA xB : ℝ) (hAB : xA < xB) :
    -- only firm B implements PP: firm A is the uniform-price leader
    (0 < xA + xB → xA + xB < 4 →
      IsLeaderOpt t xA xB (t * (xA + xB) * (xB - xA) / 2) ∧
      (∀ q : ℝ, IsLeaderOpt t xA xB q → q = t * (xA + xB) * (xB - xA) / 2) ∧
      leadProf t xA xB (t * (xA + xB) * (xB - xA) / 2) = t * (xB - xA) * (xA + xB)^2 / 8 ∧
      followProf t xA xB (t * (xA + xB) * (xB - xA) / 2) = t * (xB - xA) * (4 - xA - xB)^2 / 16) ∧
    -- only firm A implements PP: firm B is the uniform-price leader
    (-2 < xA + xB → xA + xB < 2 →
      IsLeaderOpt t xB xA (t * (xB - xA) * (2 - xA - xB) / 2) ∧
      (∀ q : ℝ, IsLeaderOpt t xB xA q → q = t * (xB - xA) * (2 - xA - xB) / 2) ∧
      followProf t xB xA (t * (xB - xA) * (2 - xA - xB) / 2) = t * (xB - xA) * (2 + xA + xB)^2 / 16 ∧
      leadProf t xB xA (t * (xB - xA) * (2 - xA - xB) / 2) = t * (xB - xA) * (2 - xA - xB)^2 / 8) := by sorry

end PPDifferentiation.Costless
