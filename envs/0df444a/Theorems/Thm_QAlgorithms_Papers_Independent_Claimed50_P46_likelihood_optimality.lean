-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P46_likelihood_optimality
-- name    : QAlgorithms.Papers.Independent.Claimed50.P46.likelihood_optimality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:17:47.430141+00:00
-- url     : https://prove2.me/theorems/40a238ab-cd73-4c20-ac8b-386b94dcbdf6
-- title:
--   Section III: generalized likelihood-test inequalities (13)–(16)
-- statement:
--   Let $n\ge1$. In the classical model, let $\rho_n$ be probability mass functions on finite or countable alphabets and let $\sigma_n$ be pointwise finite nonnegative weights, possibly of infinite total mass. In the quantum model, let $\rho_n$ be density operators and $\sigma_n$ bounded positive operators on arbitrary complex Hilbert spaces. A test is a function with values in $[0,1]$, or a quantum effect $0\le T_n\le I$, respectively. Put $\alpha_n[T_n]=\rho_n[I-T_n]$, $\beta_n[T_n]=\sigma_n[T_n]$. Write $\alpha_L,\alpha_U$ for their lower and upper asymptotic type-I errors, $\eta_L,\eta_U$ for the lower and upper limits of $-\log\alpha_n/n$, and $\zeta_L,\zeta_U$ for the analogous type-II exponents. A superscript $c$ replaces a test by its complement. All logarithms are natural, and exponent and optimization values retain both infinities. Choose any family $S_n(a)$ between the strict-positive and nonnegative likelihood spectral projections (or the corresponding classical tests); a function evaluated at $a$ means its value on this test sequence.
--
--   For every $n,a$ and every test $T_n$, put $c=e^{na}$ and $S=S_n(a)$. Then
--   $$
--   \begin{aligned}
--   \alpha_n[S]+c\beta_n[S]&\le1,\\
--   \alpha_n[S]+c\beta_n[S]&\le\alpha_n[T_n]+c\beta_n[T_n],\\
--   \alpha_n[S]&\le c\beta_n[I-S],\\
--   \alpha_n[S]+c\beta_n[I-T_n]&\le\alpha_n[T_n]+c\beta_n[I-S].
--   \end{aligned}
--   $$
--
--   These are the generalized likelihood-test optimality inequalities used by the subsequent asymptotic results.
-- source:
--   An Information-Spectrum Approach to Classical and Quantum Hypothesis Testing for Simple Hypotheses, arXiv:quant-ph/0206185v2, PDF p. 4, Section III: generalized likelihood-test inequalities (13)–(16)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46

noncomputable section

open Filter

open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsPositive State relativeEntropy)

universe u

namespace QAlgorithms.Papers.Independent.Claimed50.P46

/-- Section III, PDF pp.4–5, (13)–(16). Complementary inequalities use additions
of nonnegative extended quantities, never a difference of infinite sigma weights. -/
theorem likelihood_optimality (P : ℕ → SimpleHypothesisSystem.{u}) (hP : OriginalNormalization P)
    (S : LikelihoodFamily P) (k : ℕ) (a : ℝ) (T : SimpleHypothesisTest (P k)) :
    let c := ENNReal.ofReal (Real.exp (((k : ℝ) + 1) * a))
    testingTypeI (S.tests a k) + c * testingTypeII (S.tests a k) ≤ 1 ∧
    testingTypeI (S.tests a k) + c * testingTypeII (S.tests a k) ≤ testingTypeI T + c * testingTypeII T ∧
    testingTypeI (S.tests a k) ≤ c * testingTypeII (testRejection (S.tests a k)) ∧
    testingTypeI (S.tests a k) + c * testingTypeII (testRejection T) ≤
      testingTypeI T + c * testingTypeII (testRejection (S.tests a k)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P46

end
