-- Prove2me | Theorems.Thm_RecallTesting_Duopoly_lemma_1_equal_quality
-- name    : RecallTesting.Duopoly.lemma_1_equal_quality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:40.311927+00:00
-- url     : https://prove2.me/theorems/3f2813d1-96e4-44a6-ba07-6ac4e105fc23
-- title:
--   Lemma 1, third bullet, p. 14 — equal qualities: the unique price equilibrium is (0, 0) and profits are zero
-- statement:
--   Let $q>0$, and consider one period in which both firms sell products of the same quality $q$, to a unit mass of consumers with tastes uniform on $[0,1]$ (an indifferent consumer splits evenly between the firms).
--
--   Then $(0,0)$ is a price equilibrium, it is the only one,
--   $$p_t^i=p_t^{i'}=0,\qquad \pi_t^i=\pi_t^{i'}=0,$$
--   and the model's price and period profit for equal qualities are $0$.
--
--   This is the Bertrand case of the pricing subgame ("If both firms offer products of equal quality level, Bertrand price competition ensues, driving prices and profits to zero", p. 14). It covers every pair of identical products in the testing game: two mature products, two innovations, or two recalled innovations.
-- source:
--   Kim, Koenigsberg & Ofek, I Don’t “Recall”, SSRN working paper 3492105 (Nov. 2019), p. 14 (PDF 15), Lemma 1, third bullet, and the first sentence of §4.2

import Mathlib
import Definitions.Def_RecallTesting_Duopoly_Model

namespace RecallTesting.Duopoly

theorem lemma_1_equal_quality (q : ℝ) (hq : 0 < q) :
    IsPriceEq q q 0 0 ∧ (∀ p p' : ℝ, IsPriceEq q q p p' → p = 0 ∧ p' = 0) ∧
    eqPrice q q = 0 ∧ periodProfit q q = 0 := by sorry

end RecallTesting.Duopoly
