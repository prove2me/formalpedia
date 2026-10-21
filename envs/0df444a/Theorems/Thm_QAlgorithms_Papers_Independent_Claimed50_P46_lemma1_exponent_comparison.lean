-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P46_lemma1_exponent_comparison
-- name    : QAlgorithms.Papers.Independent.Claimed50.P46.lemma1_exponent_comparison
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:22:31.444011+00:00
-- url     : https://prove2.me/theorems/45ab54b5-4867-4a2d-8463-e19020a1bd61
-- title:
--   Lemma 1: likelihood exponent comparison (39)–(42)
-- statement:
--   Let $n\ge1$. In the classical model, let $\rho_n$ be probability mass functions on finite or countable alphabets and let $\sigma_n$ be pointwise finite nonnegative weights, possibly of infinite total mass. In the quantum model, let $\rho_n$ be density operators and $\sigma_n$ bounded positive operators on arbitrary complex Hilbert spaces. A test is a function with values in $[0,1]$, or a quantum effect $0\le T_n\le I$, respectively. Put $\alpha_n[T_n]=\rho_n[I-T_n]$, $\beta_n[T_n]=\sigma_n[T_n]$. Write $\alpha_L,\alpha_U$ for their lower and upper asymptotic type-I errors, $\eta_L,\eta_U$ for the lower and upper limits of $-\log\alpha_n/n$, and $\zeta_L,\zeta_U$ for the analogous type-II exponents. A superscript $c$ replaces a test by its complement. All logarithms are natural, and exponent and optimization values retain both infinities. Choose any family $S_n(a)$ between the strict-positive and nonnegative likelihood spectral projections (or the corresponding classical tests); a function evaluated at $a$ means its value on this test sequence.
--
--   For every real $a$ and every test sequence $T$,
--   $$
--   \zeta_L(a)\ge\min\{\zeta_L[T],a+\eta_L[T]\},\qquad
--   \eta_L(a)\ge\min\{\eta_L[T],-a+\zeta_L[T]\}.
--   $$
--   For $a<b$, both implications hold:
--   $$
--   \zeta_L(a)<\zeta_L(b)\Longrightarrow\zeta_L(a)\ge a+\eta_L(b),\qquad
--   \eta_L(a)>\eta_L(b)\Longrightarrow\eta_L(b)\ge-b+\zeta_L(a).
--   $$
--
--   These are all four exponent comparisons in Lemma 1.
-- source:
--   An Information-Spectrum Approach to Classical and Quantum Hypothesis Testing for Simple Hypotheses, arXiv:quant-ph/0206185v2, PDF p. 10, Lemma 1: likelihood exponent comparison (39)–(42)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46

noncomputable section

open Filter

open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsPositive State relativeEntropy)

universe u

namespace QAlgorithms.Papers.Independent.Claimed50.P46

/-- Lemma 1, PDF p.10: all four comparisons (39)–(42), with liminf exponents. -/
theorem lemma1_exponent_comparison (P : ℕ → SimpleHypothesisSystem.{u}) (hP : OriginalNormalization P)
    (S : LikelihoodFamily P) :
    (∀ (a : ℝ) (T : (k : ℕ) → SimpleHypothesisTest (P k)),
      min (zetaL T) ((a : EReal) + etaL T) ≤ zetaL (S.tests a) ∧
      min (etaL T) (((-a : ℝ) : EReal) + zetaL T) ≤ etaL (S.tests a)) ∧
    (∀ a b : ℝ, a < b →
      (zetaL (S.tests a) < zetaL (S.tests b) →
        (a : EReal) + etaL (S.tests b) ≤ zetaL (S.tests a)) ∧
      (etaL (S.tests b) < etaL (S.tests a) →
        ((-b : ℝ) : EReal) + zetaL (S.tests a) ≤ etaL (S.tests b))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P46

end
