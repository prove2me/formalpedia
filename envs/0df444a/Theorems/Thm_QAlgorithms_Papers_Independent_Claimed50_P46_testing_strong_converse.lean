-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P46_testing_strong_converse
-- name    : QAlgorithms.Papers.Independent.Claimed50.P46.testing_strong_converse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:21:03.960987+00:00
-- url     : https://prove2.me/theorems/1cf6b635-1473-4482-b655-ef7cbc7a29c0
-- title:
--   Remark 2: strong converse iff spectral rates coincide
-- statement:
--   Let $n\ge1$. In the classical model, let $\rho_n$ be probability mass functions on finite or countable alphabets and let $\sigma_n$ be pointwise finite nonnegative weights, possibly of infinite total mass. In the quantum model, let $\rho_n$ be density operators and $\sigma_n$ bounded positive operators on arbitrary complex Hilbert spaces. A test is a function with values in $[0,1]$, or a quantum effect $0\le T_n\le I$, respectively. Put $\alpha_n[T_n]=\rho_n[I-T_n]$, $\beta_n[T_n]=\sigma_n[T_n]$. Write $\alpha_L,\alpha_U$ for their lower and upper asymptotic type-I errors, $\eta_L,\eta_U$ for the lower and upper limits of $-\log\alpha_n/n$, and $\zeta_L,\zeta_U$ for the analogous type-II exponents. A superscript $c$ replaces a test by its complement. All logarithms are natural, and exponent and optimization values retain both infinities. Choose any family $S_n(a)$ between the strict-positive and nonnegative likelihood spectral projections (or the corresponding classical tests); a function evaluated at $a$ means its value on this test sequence.
--
--   Let $B(0)$ be the optimal exponent under vanishing type-I error, and put $D_L=D_L(0)$, $D_U=D_U(1)$, using the spectral threshold suprema of Section IV. Then
--   $$
--   D_L=D_U\quad\Longleftrightarrow\quad
--   \forall T,\ \zeta_L[T]>B(0)\ \Longrightarrow\ \alpha_n[T_n]\longrightarrow1.
--   $$
--
--   This is the necessary-and-sufficient testing strong-converse criterion.
-- source:
--   An Information-Spectrum Approach to Classical and Quantum Hypothesis Testing for Simple Hypotheses, arXiv:quant-ph/0206185v2, PDF p. 7, Remark 2: strong converse iff spectral rates coincide

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46

noncomputable section

open Filter

open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsPositive State relativeEntropy)

universe u

namespace QAlgorithms.Papers.Independent.Claimed50.P46

/-- Remark 2, PDF p.7: spectral coincidence iff every faster test has alpha tending to one. -/
theorem testing_strong_converse (P : ℕ → SimpleHypothesisSystem.{u}) (hP : OriginalNormalization P)
    (S : LikelihoodFamily P) :
    divergenceL S 0 = divergenceU S 1 ↔
      ∀ T : (k : ℕ) → SimpleHypothesisTest (P k), steinB P 0 < zetaL T →
        Tendsto (fun k => testingTypeI (T k)) atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P46

end
