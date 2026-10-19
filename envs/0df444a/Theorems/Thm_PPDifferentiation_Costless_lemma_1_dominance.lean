-- Prove2me | Theorems.Thm_PPDifferentiation_Costless_lemma_1_dominance
-- name    : PPDifferentiation.Costless.lemma_1_dominance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:26:02.831908+00:00
-- url     : https://prove2.me/theorems/b85ee97f-a179-427d-b785-dac598c0e48c
-- title:
--   Lemma 1, p. 10 — with costless PP, implementing PP is strictly dominant for both firms; both-PP profits t(x_B − x_A)(x_A + x_B)²/4, t(x_B − x_A)(2 − x_A − x_B)²/4
-- statement:
--   Let $t>0$ and let the firms be located at $x_A<x_B$ with $0<x_A+x_B<2$. When PP is costless, implementing PP is strictly dominant for both firms in the stage-2 game: the stage-3 outcomes (optimal leader prices in both orientations and a uniform-price equilibrium) exist, and for each of them
--
--   1. firm $A$ earns strictly more with PP than without, whether $B$ implements PP or not;
--   2. firm $B$ earns strictly more with PP than without, whether $A$ implements PP or not.
--
--   Consequently both firms implement PP in equilibrium, and their profits are
--   $$\pi_A=\frac{t(x_B-x_A)(x_A+x_B)^2}{4},\qquad \pi_B=\frac{t(x_B-x_A)(2-x_A-x_B)^2}{4}.$$
--
--   This is the first part of Lemma 1; it reduces the stage-1 position game to the both-PP profits used in Proposition 1.
--
--   **Formalization Note** "Both firms implement PP in equilibrium" is stated as strict dominance of PP for each firm, which makes (PP, PP) the unique equilibrium of the stage-2 game. The page says "for any firm locations $x_A\le x_B$"; the statement is posed on $x_A<x_B$, $0<x_A+x_B<2$, where the profit formulas hold and the dominance is strict (at $x_A=x_B$ all profits vanish, and at $x_A+x_B\in\{0,2\}$ one firm's profits tie at $0$). With costless PP no fixed cost is subtracted.
-- source:
--   Li, Wang, Nault, Is Personalized Pricing Profitable When Firms Can Differentiate?, working paper, SSRN abstract 3881900 (version of August 3, 2021), p. 10, Lemma 1 (first part); proof pp. 33–34, Table 3

import Mathlib
import Definitions.Def_PPDifferentiation_Costless_Setting

namespace PPDifferentiation.Costless

theorem lemma_1_dominance (t : ℝ) (ht : 0 < t) (xA xB : ℝ) (hAB : xA < xB)
    (h0 : 0 < xA + xB) (h2 : xA + xB < 2) :
    PPStrictlyDominant t xA xB ∧
    profPP t xA xB = t * (xB - xA) * (xA + xB)^2 / 4 ∧
    profPP t xB xA = t * (xB - xA) * (2 - xA - xB)^2 / 4 := by sorry

end PPDifferentiation.Costless
