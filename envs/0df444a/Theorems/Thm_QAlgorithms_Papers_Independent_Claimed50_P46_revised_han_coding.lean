-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P46_revised_han_coding
-- name    : QAlgorithms.Papers.Independent.Claimed50.P46.revised_han_coding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:31:47.951911+00:00
-- url     : https://prove2.me/theorems/654920d0-5fdf-4643-a135-cca2dba6611d
-- title:
--   Section VIII: corrected unconditional Han-form expression
-- statement:
--   Let $P_n$ be a general source on a finite or countable alphabet $X^n$, with no independence or stationarity assumption. A code has a finite nonempty message set and arbitrary stochastic encoder and decoder, each normalized on every input. Write $\gamma_n$ for its error probability, $q_n=1-\gamma_n$ for success, and $L(\Phi)=\limsup_n n^{-1}\log|\Phi_n|$ for its extended real rate. Infima below range over all such code sequences. The counting-measure testing model compares $\rho_n=P_n$ with $\sigma_n(x)=1$. Choose any allowed likelihood family. Write $t_n(a)=\rho_n[I-S_n(-a)]$ for the upper self-information tail with its matched boundary choice; its complement is the matched lower tail. Logarithms are natural and zero probability has infinite exponent.
--
--   Let $r\ge0$, $\sigma_U^*(a)=\limsup_n[-\log\rho_n[S_n(-a)]]/n$, and $b_0=\sup\{a:\sigma_U^*(a)>r\}$. With $R_e^*(r)$ the optimum rate subject to upper success exponent at most $r$,
--   $$
--   R_e^*(r)=\inf\{h\ge0:\inf_{a\in\mathbb R}\max\{\sigma_U^*(a),a-h\}\le r\}
--   =\max\{b_0-r,0\}.
--   $$
--
--   This is the corrected unconditional Han-form expression with the upper-limit spectral exponent.
-- source:
--   An Information-Spectrum Approach to Classical and Quantum Hypothesis Testing for Simple Hypotheses, arXiv:quant-ph/0206185v2, PDF p. 20, Section VIII: corrected unconditional Han-form expression

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46

noncomputable section

open Filter

open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsPositive State relativeEntropy)

universe u

namespace QAlgorithms.Papers.Independent.Claimed50.P46

/-- Section VIII, PDF p.20: corrected unconditional Han-form expression using limsup. -/
theorem revised_han_coding (P : Source.{u}) (S : LikelihoodFamily (sourceSystem P))
    (r : ℝ) (hr : 0 ≤ r) :
    codingCorrectRate P r = revisedHanRate S r ∧
    revisedHanRate S r = max (sourceCutoff S r - (r : EReal)) 0 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P46

end
