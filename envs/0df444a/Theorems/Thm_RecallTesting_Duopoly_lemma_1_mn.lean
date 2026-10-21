-- Prove2me | Theorems.Thm_RecallTesting_Duopoly_lemma_1_mn
-- name    : RecallTesting.Duopoly.lemma_1_mn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:19.994396+00:00
-- url     : https://prove2.me/theorems/6eef266a-a288-47c2-9a10-bdb1c2f5a692
-- title:
--   Lemma 1, first bullet, p. 14 — mature vs innovation: unique equilibrium prices VB/(3V+4B), 2B(V+B)/(3V+4B); profits
-- statement:
--   Let $V>0$ and $B>0$. Consider one period in which one firm sells the mature product of quality $q_L=V$ and its rival sells the innovation of quality $q_H=V+B$, to a unit mass of consumers with tastes uniform on $[0,1]$.
--
--   Then the prices
--   $$p_1^i(m,n)=\frac{VB}{3V+4B},\qquad p_1^{i'}(n,m)=\frac{2B(V+B)}{3V+4B}$$
--   form the unique price equilibrium (each is a best response among all nonnegative prices to the other, and no other price pair is an equilibrium), these are the prices $p(V,V+B)$ and $p(V+B,V)$ used by the model, and the resulting profits are
--   $$\pi_1^i(m,n)=\frac{VB(V+B)}{(3V+4B)^2},\qquad \pi_1^{i'}(n,m)=\frac{4B(V+B)^2}{(3V+4B)^2}.$$
--
--   This is the first case of the pricing subgame: it gives the first-period profits of a tester facing a non-tester.
--
--   **Formalization Note** The equilibrium claim is global: deviations range over all nonnegative prices, including undercutting into the rival's segment. Profits are computed from the measure-theoretic demand of the model, not from a closed form.
-- source:
--   Kim, Koenigsberg & Ofek, I Don’t “Recall”, SSRN working paper 3492105 (Nov. 2019), p. 14 (PDF 15), Lemma 1, first bullet; proof p. 35 (PDF 36)

import Mathlib
import Definitions.Def_RecallTesting_Duopoly_Model

namespace RecallTesting.Duopoly

theorem lemma_1_mn (V B : ℝ) (hV : 0 < V) (hB : 0 < B) :
    IsPriceEq V (V + B) (V * B / (3 * V + 4 * B)) (2 * B * (V + B) / (3 * V + 4 * B)) ∧
    (∀ p p' : ℝ, IsPriceEq V (V + B) p p' →
      p = V * B / (3 * V + 4 * B) ∧ p' = 2 * B * (V + B) / (3 * V + 4 * B)) ∧
    eqPrice V (V + B) = V * B / (3 * V + 4 * B) ∧
    eqPrice (V + B) V = 2 * B * (V + B) / (3 * V + 4 * B) ∧
    periodProfit V (V + B) = V * B * (V + B) / (3 * V + 4 * B) ^ 2 ∧
    periodProfit (V + B) V = 4 * B * (V + B) ^ 2 / (3 * V + 4 * B) ^ 2 := by sorry

end RecallTesting.Duopoly
