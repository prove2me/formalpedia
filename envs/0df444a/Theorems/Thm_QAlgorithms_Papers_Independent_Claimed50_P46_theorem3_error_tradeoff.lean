-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P46_theorem3_error_tradeoff
-- name    : QAlgorithms.Papers.Independent.Claimed50.P46.theorem3_error_tradeoff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:23:04.464742+00:00
-- url     : https://prove2.me/theorems/264d2478-75f3-40c5-9208-c92dc852d626
-- title:
--   Theorem 3: full error-exponent tradeoff
-- statement:
--   Let $n\ge1$. In the classical model, let $\rho_n$ be probability mass functions on finite or countable alphabets and let $\sigma_n$ be pointwise finite nonnegative weights, possibly of infinite total mass. In the quantum model, let $\rho_n$ be density operators and $\sigma_n$ bounded positive operators on arbitrary complex Hilbert spaces. A test is a function with values in $[0,1]$, or a quantum effect $0\le T_n\le I$, respectively. Put $\alpha_n[T_n]=\rho_n[I-T_n]$, $\beta_n[T_n]=\sigma_n[T_n]$. Write $\alpha_L,\alpha_U$ for their lower and upper asymptotic type-I errors, $\eta_L,\eta_U$ for the lower and upper limits of $-\log\alpha_n/n$, and $\zeta_L,\zeta_U$ for the analogous type-II exponents. A superscript $c$ replaces a test by its complement. All logarithms are natural, and exponent and optimization values retain both infinities. Choose any family $S_n(a)$ between the strict-positive and nonnegative likelihood spectral projections (or the corresponding classical tests); a function evaluated at $a$ means its value on this test sequence.
--
--   For real $r\ge0$, define $B_e(r)=\sup\{\zeta_L[T]:\eta_L[T]\ge r\}$ and
--   $$
--   a_0=\sup\{a':\exists a,\ \eta_L(a)\ge r,\ \zeta_L(a')=\zeta_L(a)\}.
--   $$
--   Then
--   $$
--   B_e(r)=\sup_{a:\eta_L(a)\ge r}\zeta_L(a)
--   =\inf_{a:\eta_L(a)<r}\{a+\eta_L(a)\}
--   =\zeta_L(a_0-0)=a_0+\eta_L(a_0+0).
--   $$
--   The cutoff expressions use the source's singular-case convention: their common value is $-\infty$ for an empty feasible threshold set and $+\infty$ when every threshold is feasible. At a finite cutoff, the last expression uses the ordinary right limit. The left-cutoff expression is the supremum over real thresholds below the cutoff.
--
--   This gives the full error-exponent tradeoff, including the singular cases.
--
--   At $a_0=-\infty$, the left-cutoff expression means the empty strict-threshold supremum $-\infty$. This is a correction to the printed monotone endpoint limit: on a singleton, $\rho_n=1$ and $\sigma_n=e^{n^2}$ give $\zeta(a)=+\infty$ at every real threshold, whereas $B_e(r)=-\infty$ for $r>0$.
-- source:
--   An Information-Spectrum Approach to Classical and Quantum Hypothesis Testing for Simple Hypotheses, arXiv:quant-ph/0206185v2, PDF p. 10, Theorem 3: full error-exponent tradeoff

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46

noncomputable section

open Filter

open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsPositive State relativeEntropy)

universe u

namespace QAlgorithms.Papers.Independent.Claimed50.P46

/-- Theorem 3, PDF pp.10–11: all characterizations, with Remark 6's singular endpoints.
Printed: Be=zeta(a0-0), using Remark 5's monotone endpoint convention.
Changed: at a0=-infinity use the empty strict-threshold supremum -infinity.
Why: on a singleton, rho_n=1 and sigma_n=exp(n^2) give eta(a)=0 and
zeta(a)=+infinity for every finite a, but Be(r)=-infinity for r>0.
The finite-cutoff left limit and all other operational identities are retained. -/
theorem theorem3_error_tradeoff (P : ℕ → SimpleHypothesisSystem.{u}) (hP : OriginalNormalization P)
    (S : LikelihoodFamily P) (r : ℝ) (hr : 0 ≤ r) :
    errorTradeoff P r = sSup {z | ∃ a : ℝ, (r : EReal) ≤ etaL (S.tests a) ∧
      z = zetaL (S.tests a)} ∧
    errorTradeoff P r = sInf {z | ∃ a : ℝ, etaL (S.tests a) < (r : EReal) ∧
      z = (a : EReal) + etaL (S.tests a)} ∧
    errorTradeoff P r = increasingLeft (fun a => zetaL (S.tests a)) (errorCutoff S r) ∧
    errorTradeoff P r = errorCutoffValue S r := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P46

end
