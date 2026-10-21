-- Prove2me | Theorems.Thm_RecallTesting_Duopoly_lemma_1_nr
-- name    : RecallTesting.Duopoly.lemma_1_nr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:15.039763+00:00
-- url     : https://prove2.me/theorems/46561a75-151a-4b68-985b-269db1d65e5b
-- title:
--   Lemma 1, second bullet, p. 14 — innovation vs recalled innovation: unique equilibrium prices 2(V+B)γ/(3+γ), (V+B)(1−γ)γ/(3+γ); profits
-- statement:
--   Let $V>0$, $B>0$ and $0<\gamma<1$. Consider one period in which one firm sells the innovation of quality $q_H=V+B$ and its rival sells a recalled innovation of quality $q_L=(V+B)(1-\gamma)$, to a unit mass of consumers with tastes uniform on $[0,1]$.
--
--   Then the prices
--   $$p_2^i(n,r)=\frac{2(V+B)\gamma}{3+\gamma},\qquad p_2^{i'}(r,n)=\frac{(V+B)(1-\gamma)\gamma}{3+\gamma}$$
--   form the unique price equilibrium, they are the prices used by the model, and the resulting profits are
--   $$\pi_2^i(n,r)=\frac{4(V+B)\gamma}{(3+\gamma)^2},\qquad \pi_2^{i'}(r,n)=\frac{(V+B)(1-\gamma)\gamma}{(3+\gamma)^2}.$$
--
--   This is the second case of the pricing subgame: it gives the second-period profits when exactly one of two launched innovations was recalled.
--
--   **Formalization Note** As in the first bullet, deviations range over all nonnegative prices and profits are computed from demand.
-- source:
--   Kim, Koenigsberg & Ofek, I Don’t “Recall”, SSRN working paper 3492105 (Nov. 2019), p. 14 (PDF 15), Lemma 1, second bullet; proof pp. 35–36 (PDF 36–37)

import Mathlib
import Definitions.Def_RecallTesting_Duopoly_Model

namespace RecallTesting.Duopoly

theorem lemma_1_nr (V B γ : ℝ) (hV : 0 < V) (hB : 0 < B) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    IsPriceEq (V + B) ((V + B) * (1 - γ))
      (2 * (V + B) * γ / (3 + γ)) ((V + B) * (1 - γ) * γ / (3 + γ)) ∧
    (∀ p p' : ℝ, IsPriceEq (V + B) ((V + B) * (1 - γ)) p p' →
      p = 2 * (V + B) * γ / (3 + γ) ∧
      p' = (V + B) * (1 - γ) * γ / (3 + γ)) ∧
    eqPrice (V + B) ((V + B) * (1 - γ)) = 2 * (V + B) * γ / (3 + γ) ∧
    eqPrice ((V + B) * (1 - γ)) (V + B) = (V + B) * (1 - γ) * γ / (3 + γ) ∧
    periodProfit (V + B) ((V + B) * (1 - γ)) = 4 * (V + B) * γ / (3 + γ) ^ 2 ∧
    periodProfit ((V + B) * (1 - γ)) (V + B) = (V + B) * (1 - γ) * γ / (3 + γ) ^ 2 := by sorry

end RecallTesting.Duopoly
