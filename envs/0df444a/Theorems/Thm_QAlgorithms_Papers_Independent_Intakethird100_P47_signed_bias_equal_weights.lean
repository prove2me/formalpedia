-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P47_signed_bias_equal_weights
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P47.signed_bias_equal_weights
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T05:34:14.902072+00:00
-- url     : https://prove2.me/theorems/52351c7c-542c-4260-abcd-709e2be81c14
-- title:
--   Equal weights are forced for four signed biases
-- statement:
--   Let $0<p_A,p_B<1$ and $0<\epsilon\le\min(p_A,1-p_A,p_B,1-p_B)$. For $e=(e_A,e_B)\in\{-1,+1\}^2$, let $w_e$ be the independent binary setting law with probabilities of input zero $p_A+e_A\epsilon$ and $p_B+e_B\epsilon$. Let $w$ be the product law with parameters $p_A,p_B$, and let $t_e\ge0$ sum to one. Then
--   $$
--   \bigl(\forall A,B,\ \sum_e t_e w_e(A,B)=w(A,B)\bigr)
--   \quad\Longleftrightarrow\quad \forall e,\ t_e=\tfrac14.
--   $$
--   This is uniqueness of the prior mixture producing the nominal input distribution. It does not give the bias-label distribution after acceptance.
-- source:
--   Device-independent quantum key distribution based on measurement inputs, arXiv:1308.6447v3, PDF p. 4, III: equal weights of four signed biases

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P47

namespace QAlgorithms.Papers.Independent.Intakethird100.P47

open scoped ComplexConjugate

open scoped BigOperators

/-- III, PDF p.4: the four signed-bias mixture equals (5) exactly for equal weights.
The necessary exclusion epsilon=0 is explicit; endpoint component probabilities may be zero. -/
theorem signed_bias_equal_weights (pA pB epsilon : ℝ)
    (hA : 0 < pA ∧ pA < 1) (hB : 0 < pB ∧ pB < 1)
    (he : 0 < epsilon)
    (heA : epsilon ≤ pA ∧ epsilon ≤ 1 - pA)
    (heB : epsilon ≤ pB ∧ epsilon ≤ 1 - pB)
    (t : (Bool × Bool) → ℝ) (ht : ∀ e, 0 ≤ t e) (hsum : ∑ e, t e = 1) :
    ((∀ A B, (∑ e, t e * biasedInput pA pB epsilon e A B) = binarySettingLaw pA pB A B) ↔
      ∀ e, t e = 1 / 4) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P47
