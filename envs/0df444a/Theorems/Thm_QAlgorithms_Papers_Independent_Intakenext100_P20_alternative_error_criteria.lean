-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P20_alternative_error_criteria
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P20.alternative_error_criteria
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:35:36.567561+00:00
-- url     : https://prove2.me/theorems/c32e7958-6868-4487-83d4-bc6779be5b9c
-- title:
--   Remark 2, (14)–(17): alternative error criteria
-- statement:
--   Let $\Xi$ be an arbitrary discrete label set and let $\mathcal H$ be a nonzero finite-dimensional complex Hilbert space. The source consists of normalized pure states $\rho_i$ and probabilities $p_i\ge0$ with $\sum_i p_i=1$; write $\rho_p=\sum_i p_i\rho_i$. Each memory space is finite and nonzero. Blind encoders and decoders are CPTP; a visible encoder maps labels to normalized density operators. A blind encoder is fixed before its input label.
--
--   For positive block length $n$, the word probabilities and states are the independent products of the source probabilities and states. Admissible code sequences satisfy $\limsup_n n^{-1}\log\dim\mathcal K_n\le R$. An error exponent is the supremum over admissible sequences of $\liminf_n -n^{-1}\log\epsilon_n$; a success exponent is the infimum of $\liminf_n -n^{-1}\log(1-\epsilon_n)$. Logarithms are natural, and $-\log0=+\infty$.
--
--   For either coding model define $\epsilon_b=\sum_i p_i(1-\sqrt{\operatorname{Tr}(D(F(i))\rho_i)})$, interpreting $F(i)=E(\rho_i)$ in the blind case. Subscript $b$ means the optimized exponent formed with this loss. Then
--
--   $$r_{e,B,b}(R)=r_{e,B}(R),\quad r_{e,V,b}(R)=r_{e,V}(R),$$
--   $$r^*_{e,B}(R)\ge r^*_{e,B,b}(R),\quad r^*_{e,V}(R)\ge r^*_{e,V,b}(R).$$
--
--   Thus the square-root-overlap criterion preserves the optimal error exponent and gives the stated comparisons for success exponents.
-- source:
--   Exponents of quantum fixed-length pure state source coding, arXiv:quant-ph/0202002v6, PDF p. 3, Remark 2, (14)–(17): alternative error criteria

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P20

noncomputable section

open scoped Matrix ENNReal ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P20

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P47 (IsProbability)

open QAlgorithms.Papers.Independent.Information100.P53 (SpectralData)

open QAlgorithms.Papers.Independent.Gap48.P19 (shannonNats)

open QAlgorithms.Papers.Independent.Dependency50.P28 (classicalD)

attribute [local instance] Classical.propDecidable

/-- Remark 2, PDF p.3, (14)-(17), Appendix C pp.10-11: unchanged error
exponents and the stated one-sided success-exponent comparisons.
Printed blind-loss input: F(rho_i); changed to E(rho_i), because Section II
defines E as the blind quantum encoder and Appendix C uses that model. -/
theorem alternative_error_criteria {L : Type*} {d : ℕ} (S : DiscretePureSource L d) (R : ℝ) :
    blindExponent S R true false = blindExponent S R false false ∧
    visibleExponent S R true false = visibleExponent S R false false ∧
    blindExponent S R true true ≤ blindExponent S R false true ∧
    visibleExponent S R true true ≤ visibleExponent S R false true := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P20

end
