-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P46_theorem7_correct_decoding
-- name    : QAlgorithms.Papers.Independent.Claimed50.P46.theorem7_correct_decoding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:31:14.398993+00:00
-- url     : https://prove2.me/theorems/59bbf74f-b969-4867-85f1-dd3cbc29377c
-- title:
--   Theorem 7: general correct-decoding exponent tradeoff (109)
-- statement:
--   Let $P_n$ be a general source on a finite or countable alphabet $X^n$, with no independence or stationarity assumption. A code has a finite nonempty message set and arbitrary stochastic encoder and decoder, each normalized on every input. Write $\gamma_n$ for its error probability, $q_n=1-\gamma_n$ for success, and $L(\Phi)=\limsup_n n^{-1}\log|\Phi_n|$ for its extended real rate. Infima below range over all such code sequences. The counting-measure testing model compares $\rho_n=P_n$ with $\sigma_n(x)=1$. Choose any allowed likelihood family. Write $t_n(a)=\rho_n[I-S_n(-a)]$ for the upper self-information tail with its matched boundary choice; its complement is the matched lower tail. Logarithms are natural and zero probability has infinite exponent.
--
--   For real $r\ge0$, define $R_e^*(r)=\inf\{L(\Phi):\limsup_n[-\log q_n]/n\le r\}$ and
--   $$
--   \sigma_U^*(a)=\limsup_n\frac{-\log\rho_n[S_n(-a)]}{n},\qquad
--   b_0=\sup\{a:\sigma_U^*(a)>r\}=\inf\{a:\sigma_U^*(a)\le r\}.
--   $$
--   Then
--   $$
--   R_e^*(r)=\max\{b_0-r,0\}.
--   $$
--
--   This is the unconditional general correct-decoding exponent tradeoff.
-- source:
--   An Information-Spectrum Approach to Classical and Quantum Hypothesis Testing for Simple Hypotheses, arXiv:quant-ph/0206185v2, PDF p. 19, Theorem 7: general correct-decoding exponent tradeoff (109)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46

noncomputable section

open Filter

open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsPositive State relativeEntropy)

universe u

namespace QAlgorithms.Papers.Independent.Claimed50.P46

/-- Theorem 7, PDF p.19, (109): limsup tail exponent; the maximum with zero
expresses the nonnegative rate of every finite nonempty code. -/
theorem theorem7_correct_decoding (P : Source.{u}) (S : LikelihoodFamily (sourceSystem P))
    (r : ℝ) (hr : 0 ≤ r) :
    codingCorrectRate P r = max (sourceCutoff S r - (r : EReal)) 0 ∧
    sourceCutoff S r = sInf {z | ∃ a : ℝ, sourceSigmaStarU S a ≤ (r : EReal) ∧ z = (a : EReal)} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P46

end
