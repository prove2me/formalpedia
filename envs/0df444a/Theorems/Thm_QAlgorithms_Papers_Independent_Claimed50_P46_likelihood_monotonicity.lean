-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P46_likelihood_monotonicity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P46.likelihood_monotonicity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:18:40.571224+00:00
-- url     : https://prove2.me/theorems/7950a4d7-f854-4178-b536-88c1130be53f
-- title:
--   Section III: likelihood errors are monotone, (17)–(19)
-- statement:
--   Let $n\ge1$. In the classical model, let $\rho_n$ be probability mass functions on finite or countable alphabets and let $\sigma_n$ be pointwise finite nonnegative weights, possibly of infinite total mass. In the quantum model, let $\rho_n$ be density operators and $\sigma_n$ bounded positive operators on arbitrary complex Hilbert spaces. A test is a function with values in $[0,1]$, or a quantum effect $0\le T_n\le I$, respectively. Put $\alpha_n[T_n]=\rho_n[I-T_n]$, $\beta_n[T_n]=\sigma_n[T_n]$. Write $\alpha_L,\alpha_U$ for their lower and upper asymptotic type-I errors, $\eta_L,\eta_U$ for the lower and upper limits of $-\log\alpha_n/n$, and $\zeta_L,\zeta_U$ for the analogous type-II exponents. A superscript $c$ replaces a test by its complement. All logarithms are natural, and exponent and optimization values retain both infinities. Choose any family $S_n(a)$ between the strict-positive and nonnegative likelihood spectral projections (or the corresponding classical tests); a function evaluated at $a$ means its value on this test sequence.
--
--   If $a<b$, then for every block
--   $$
--   \alpha_n(a)\le\alpha_n(b),\qquad\beta_n(a)\ge\beta_n(b).
--   $$
--   The finite-block type-I exponents and both their asymptotic limits are nonincreasing; type-II exponents and both their limits are nondecreasing. Complementary type-II exponents and both their limits are nonincreasing. Moreover,
--   $$
--   \zeta_L(a)\ge a\quad(a\in\mathbb R).
--   $$
--
--   This records both error monotonicity and its exponent consequences.
-- source:
--   An Information-Spectrum Approach to Classical and Quantum Hypothesis Testing for Simple Hypotheses, arXiv:quant-ph/0206185v2, PDF p. 5, Section III: likelihood errors are monotone, (17)–(19)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46

noncomputable section

open Filter

open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsPositive State relativeEntropy)

universe u

namespace QAlgorithms.Papers.Independent.Claimed50.P46

/-- Section III, PDF p.5, (17),(19), and the stated exponent monotonicities. -/
theorem likelihood_monotonicity (P : ℕ → SimpleHypothesisSystem.{u}) (hP : OriginalNormalization P)
    (S : LikelihoodFamily P) :
    (∀ k a b, a < b → testingTypeI (S.tests a k) ≤ testingTypeI (S.tests b k) ∧
      testingTypeII (S.tests b k) ≤ testingTypeII (S.tests a k)) ∧
    (∀ k, Antitone (fun a => blockErrorExponent k (testingTypeI (S.tests a k))) ∧
      Monotone (fun a => blockErrorExponent k (testingTypeII (S.tests a k)))) ∧
    Antitone (fun a => etaL (S.tests a)) ∧ Antitone (fun a => etaU (S.tests a)) ∧
    Monotone (fun a => zetaL (S.tests a)) ∧ Monotone (fun a => zetaU (S.tests a)) ∧
    (∀ k, Antitone (fun a => blockErrorExponent k (testingTypeII (testRejection (S.tests a k))))) ∧
    Antitone (fun a => zetaLc (S.tests a)) ∧ Antitone (fun a => zetaUc (S.tests a)) ∧
    (∀ a : ℝ, (a : EReal) ≤ zetaL (S.tests a)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P46

end
