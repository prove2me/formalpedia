-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P46_stein_attainment
-- name    : QAlgorithms.Papers.Independent.Claimed50.P46.stein_attainment
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:19:27.67352+00:00
-- url     : https://prove2.me/theorems/24752af5-abb2-44b3-8bad-86d35f357bce
-- title:
--   Section IV: attained optimum and one-sided continuity, (20)–(21)
-- statement:
--   Let $n\ge1$. In the classical model, let $\rho_n$ be probability mass functions on finite or countable alphabets and let $\sigma_n$ be pointwise finite nonnegative weights, possibly of infinite total mass. In the quantum model, let $\rho_n$ be density operators and $\sigma_n$ bounded positive operators on arbitrary complex Hilbert spaces. A test is a function with values in $[0,1]$, or a quantum effect $0\le T_n\le I$, respectively. Put $\alpha_n[T_n]=\rho_n[I-T_n]$, $\beta_n[T_n]=\sigma_n[T_n]$. Write $\alpha_L,\alpha_U$ for their lower and upper asymptotic type-I errors, $\eta_L,\eta_U$ for the lower and upper limits of $-\log\alpha_n/n$, and $\zeta_L,\zeta_U$ for the analogous type-II exponents. A superscript $c$ replaces a test by its complement. All logarithms are natural, and exponent and optimization values retain both infinities. Choose any family $S_n(a)$ between the strict-positive and nonnegative likelihood spectral projections (or the corresponding classical tests); a function evaluated at $a$ means its value on this test sequence.
--
--   Define $B(\varepsilon)=\sup\{\zeta_L[T]:\alpha_U[T]\le\varepsilon\}$ and $B^\dagger(\varepsilon)=\sup\{\zeta_L[T]:\alpha_L[T]<\varepsilon\}$. For $0\le\varepsilon<1$, an admissible test sequence actually attains $B(\varepsilon)$, including when this value is infinite, and
--   $$
--   B(\varepsilon)=\inf_{\varepsilon<\varepsilon'\le1}B(\varepsilon').
--   $$
--   For $0<\varepsilon\le1$,
--   $$
--   B^\dagger(\varepsilon)=\sup_{0\le\varepsilon'<\varepsilon}B^\dagger(\varepsilon').
--   $$
--
--   This gives the attained Stein optimum and the two one-sided continuity properties.
-- source:
--   An Information-Spectrum Approach to Classical and Quantum Hypothesis Testing for Simple Hypotheses, arXiv:quant-ph/0206185v2, PDF p. 6, Section IV: attained optimum and one-sided continuity, (20)–(21)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46

noncomputable section

open Filter

open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsPositive State relativeEntropy)

universe u

namespace QAlgorithms.Papers.Independent.Claimed50.P46

/-- Section IV, PDF p.6, (20)–(21): actual attainment, even at an infinite optimum. -/
theorem stein_attainment (P : ℕ → SimpleHypothesisSystem.{u}) (hP : OriginalNormalization P) :
    (∀ eps : ℝ, 0 ≤ eps → eps < 1 →
      (∃ T : (k : ℕ) → SimpleHypothesisTest (P k), alphaU T ≤ ENNReal.ofReal eps ∧
        zetaL T = steinB P eps) ∧
      steinB P eps = sInf {z | ∃ e : ℝ, eps < e ∧ e ≤ 1 ∧ z = steinB P e}) ∧
    (∀ eps : ℝ, 0 < eps → eps ≤ 1 →
      steinBdag P eps = sSup {z | ∃ e : ℝ, 0 ≤ e ∧ e < eps ∧ z = steinBdag P e}) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P46

end
