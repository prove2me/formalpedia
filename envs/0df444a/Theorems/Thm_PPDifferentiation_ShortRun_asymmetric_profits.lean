-- Prove2me | Theorems.Thm_PPDifferentiation_ShortRun_asymmetric_profits
-- name    : PPDifferentiation.ShortRun.asymmetric_profits
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T12:59:18.303355+00:00
-- url     : https://prove2.me/theorems/21623e29-371e-4bde-8bc0-b0c3839fca9f
-- title:
--   §6 — asymmetric optimal leader price and gross profits
-- statement:
--   Suppose $t>0$, $x_A<x_B$, and $-2<x_A+x_B<2$. Firm A uses personalized pricing and is the follower; B posts one uniform price first. The unique optimal leader price is
--
--   $$p_B=\frac{t(x_B-x_A)(2-x_A-x_B)}{2}.$$
--
--   The resulting gross profits are $t(x_B-x_A)(2+x_A+x_B)^2/16$ for A and $t(x_B-x_A)(2-x_A-x_B)^2/8$ for B. The statement links the Section 6 formulas to the pricing primitives rather than defining profits by those formulas.
--
--   **Formalization Note** The strict location and sum bounds select the interior demand regime. The leader's optimality ranges over all real prices; an indifferent consumer buys from the targeting follower.
-- source:
--   Li, Wang, Nault, Is Personalized Pricing Profitable When Firms Can Differentiate?, working paper, SSRN abstract 3881900 (version of August 3, 2021), §6, p. 24, “Only one firm implements PP”; Appendix A, p. 33, proof of Lemma 1

import Mathlib
import Definitions.Def_PPDifferentiation_ShortRun_Setting

namespace PPDifferentiation.ShortRun

theorem asymmetric_profits (t xA xB : ℝ) (ht : 0 < t)
    (hord : xA < xB) (hlo : -2 < xA + xB) (hhi : xA + xB < 2) :
    let p := t * (2 - xA - xB) * (xB - xA) / 2
    PPDifferentiation.Costless.IsLeaderOpt t xB xA p ∧
    (∀ q : ℝ, PPDifferentiation.Costless.IsLeaderOpt t xB xA q → q = p) ∧
    PPDifferentiation.Costless.followProf t xB xA p = t * (xB - xA) * (2 + xA + xB)^2 / 16 ∧
    PPDifferentiation.Costless.leadProf t xB xA p = t * (xB - xA) * (2 - xA - xB)^2 / 8 := by sorry

end PPDifferentiation.ShortRun
