-- Prove2me | Theorems.Thm_PPDifferentiation_Costless_both_pp_profits
-- name    : PPDifferentiation.Costless.both_pp_profits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:26:00.794042+00:00
-- url     : https://prove2.me/theorems/03bc1dff-9673-43f9-a9d4-dd91311da866
-- title:
--   Appendix A, p. 33 — both firms with PP: π_A = t(x_B − x_A)(x_A + x_B)²/4, π_B = t(x_B − x_A)(2 − x_A − x_B)²/4
-- statement:
--   Let $t>0$ and let firms $A$ and $B$ be located at $x_A\le x_B$ with $0\le x_A+x_B\le 2$. When both firms implement personalized pricing and compete à la Bertrand for each consumer $x\in[0,1]$, firm $A$ wins the consumers left of the midpoint $x_0=(x_A+x_B)/2$ and firm $B$ those right of it, and the resulting profits are
--   $$\pi^{PP}_t(x_A,x_B)=\frac{t(x_B-x_A)(x_A+x_B)^2}{4},\qquad \pi^{PP}_t(x_B,x_A)=\frac{t(x_B-x_A)(2-x_A-x_B)^2}{4}.$$
--
--   These are the profits of the both-PP cell of the stage-2 payoff matrix (Table 3) and the payoffs of the position game of Proposition 1.
--
--   **Formalization Note** The page states the formulas "assuming that $x_A\le x_B$"; they also need the midpoint $x_0$ in $[0,1]$, i.e. $0\le x_A+x_B\le 2$, which is added (outside this range one firm serves the whole market and the formulas fail). The profits are the Bertrand integrals of the Setting, not definitions by formula.
-- source:
--   Li, Wang, Nault, Is Personalized Pricing Profitable When Firms Can Differentiate?, working paper, SSRN abstract 3881900 (version of August 3, 2021), p. 33, Appendix A, proof of Lemma 1 (both firms implement PP)

import Mathlib
import Definitions.Def_PPDifferentiation_Costless_Setting

namespace PPDifferentiation.Costless

theorem both_pp_profits (t : ℝ) (ht : 0 < t) (xA xB : ℝ) (hAB : xA ≤ xB)
    (h0 : 0 ≤ xA + xB) (h2 : xA + xB ≤ 2) :
    profPP t xA xB = t * (xB - xA) * (xA + xB)^2 / 4 ∧
    profPP t xB xA = t * (xB - xA) * (2 - xA - xB)^2 / 4 := by sorry

end PPDifferentiation.Costless
