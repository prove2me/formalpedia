-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P11_hybrid_ratePair
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P11.hybrid_ratePair
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:50:42.846345+00:00
-- url     : https://prove2.me/theorems/410d75d3-1399-4969-8a35-cff9e718fec8
-- title:
--   Achievable hybrid rate for the displayed opposite-parity family
-- statement:
--   Let $p_0,p_1\ge0$ sum to one, and let $\alpha_i,\beta_i\in\mathbb C$ satisfy $|\alpha_i|^2+|\beta_i|^2=1$. Consider the displayed family
--
--   $$
--   |\phi_0\rangle=\alpha_0|00\rangle+\beta_0|11\rangle,\qquad
--   |\phi_1\rangle=\alpha_1|01\rangle+\beta_1|10\rangle.
--   $$
--
--   Write $\rho=\sum_i p_i|\phi_i\rangle\langle\phi_i|$ and $\rho_B=\operatorname{Tr}_A\rho$. On measuring Alice in the computational basis, let $q_j$ be the probability of outcome $j$, and $\omega_j$ Bob's conditional density. Explicitly,
--
--   $$
--   \begin{aligned}
--   q_0&=\sum_i p_i|\alpha_i|^2,&q_1&=\sum_i p_i|\beta_i|^2,\\
--   \omega_0&=q_0^{-1}\sum_i p_i|\alpha_i|^2|i\rangle\langle i|,&
--   \omega_1&=q_1^{-1}\sum_i p_i|\beta_i|^2|1-i\rangle\langle1-i|.
--   \end{aligned}
--   $$
--
--   At a zero-probability outcome, choose $\omega_j=|0\rangle\langle0|$; its weighted contribution vanishes. Define $\chi'=S(\sum_jq_j\omega_j)-\sum_jq_jS(\omega_j)$, $a=H(q)-\chi'$, and $b=1+S(\rho_B)-S(\rho)$, with all entropies in bits and $H(q)$ the classical label entropy. Then
--
--   $$
--   \left(R_A,R_B\right)=\left(\frac{a}{a+b},\ S(\rho_B)\right)
--   \quad\text{is achievable}.
--   $$
--
--   An achievable pair uses independent blind local CPTP encoders, one noiseless quantum link from each sender, and a joint CPTP decoder, without supplied shared entanglement or side messages. For every $\delta,\epsilon>0$, every sufficiently large positive integer blocklength $n$ admits positive compressed dimensions $d_A,d_B$ with $\log_2(d_A)/n\le R_A+\delta$, $\log_2(d_B)/n\le R_B+\delta$, and ensemble-average pure-input overlap with the reconstructed density operator at least $1-\epsilon$. Draws are independent and identically distributed; this is squared fidelity, without a purifying reference.
--
--   The denominator satisfies $a+b\ge1$ for this family, so no additional nonzero-denominator hypothesis is needed. This hybrid coding rate is restricted to the displayed family and does not assert the false universal local-unitary normal form printed immediately before it.
-- source:
--   On the distributed compression of quantum information, arXiv:quant-ph/0403042v3, PDF p. 13, Section V.B (37): hybrid achievable rate for the displayed family

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P11

open MeasureTheory Filter

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Dependency50.P19 (both)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.12–14, Section V.B, (37): the displayed-family hybrid rate is achievable
with Bob at S(E_B). The false universal normal-form claim is not a hypothesis.
No free classical side channel is supplied. -/
theorem hybrid_ratePair (p : Bool → ℝ) (hp : ∀ i, 0 ≤ p i)
    (htotal : ∑ i, p i = 1) (alpha beta : Bool → ℂ)
    (hcoeff : ∀ i, Complex.normSq (alpha i) + Complex.normSq (beta i) = 1) :
    FiniteAchievable p (hybridVector alpha beta) (hybridRateA p alpha beta)
      (vnEntropy (traceLeft (sourceMean p (hybridVector alpha beta)))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P11

end
