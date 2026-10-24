-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P38_question4_equivalence
-- name    : QAlgorithms.Papers.Independent.Support50.P38.question4_equivalence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:57:43.443552+00:00
-- url     : https://prove2.me/theorems/01c3353f-9584-47b3-830a-eac5bb27b2f5
-- title:
--   Equivalence of the two global compression questions
-- statement:
--   Consider the following assertions over every pair of finite nonempty alphabets, every input law $P$, and every stochastic channel $W$, with base-two information $I(P;W)$. Assertion $A$ states that for each $0<\lambda<1$, the minimum ordinary code size $M(n,\lambda)$ satisfies $\log_2M(n,\lambda)/n\to I(P;W)$. Assertion $B$ states that for every $0<\lambda<1$, $\epsilon,\delta>0$, and all sufficiently large positive $n$, there is a single ordinary code with average block error at most $\lambda$ and
--
--   $$
--   \frac{\log_2|C|}{n}\le I(P;W)+\epsilon,\qquad
--   \forall x\in T^n_{P,\delta},\quad d_{\rm TV}(W_x^n,\widehat W_n(x))\le\lambda.
--   $$
--   The typical set uses the count tolerance $\delta\sqrt{nP(a)(1-P(a))}$ for each letter $a$. Then
--
--   $$A\iff B.$$
--
--   This equivalence concerns universal affirmative answers; it does not assert either open assertion.
-- source:
--   Compression of sources of probability distributions and density operators, arXiv:quant-ph/0208131v1, PDF p. 3, Paragraph after (10)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P38

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

attribute [local instance] Classical.propDecidable

/-- PDF p.3, paragraph following (10): equivalence of affirmative answers to the two
GLOBAL questions. Neither open assertion is promoted to an unconditional theorem. -/
theorem question4_equivalence : QuestionFour ↔ QuestionFourPrime := by sorry

end QAlgorithms.Papers.Independent.Support50.P38

end
