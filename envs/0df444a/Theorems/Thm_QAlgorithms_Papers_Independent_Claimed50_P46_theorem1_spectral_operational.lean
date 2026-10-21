-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P46_theorem1_spectral_operational
-- name    : QAlgorithms.Papers.Independent.Claimed50.P46.theorem1_spectral_operational
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:20:16.527993+00:00
-- url     : https://prove2.me/theorems/183cfbbc-e3e4-4ad6-959e-633a44a46b02
-- title:
--   Theorem 1: general operational exponents equal spectral divergence rates (24)–(27)
-- statement:
--   Let $n\ge1$. In the classical model, let $\rho_n$ be probability mass functions on finite or countable alphabets and let $\sigma_n$ be pointwise finite nonnegative weights, possibly of infinite total mass. In the quantum model, let $\rho_n$ be density operators and $\sigma_n$ bounded positive operators on arbitrary complex Hilbert spaces. A test is a function with values in $[0,1]$, or a quantum effect $0\le T_n\le I$, respectively. Put $\alpha_n[T_n]=\rho_n[I-T_n]$, $\beta_n[T_n]=\sigma_n[T_n]$. Write $\alpha_L,\alpha_U$ for their lower and upper asymptotic type-I errors, $\eta_L,\eta_U$ for the lower and upper limits of $-\log\alpha_n/n$, and $\zeta_L,\zeta_U$ for the analogous type-II exponents. A superscript $c$ replaces a test by its complement. All logarithms are natural, and exponent and optimization values retain both infinities. Choose any family $S_n(a)$ between the strict-positive and nonnegative likelihood spectral projections (or the corresponding classical tests); a function evaluated at $a$ means its value on this test sequence.
--
--   Let $B,B^\dagger$ be the operational suprema with constraints $\alpha_U[T]\le\varepsilon$ and $\alpha_L[T]<\varepsilon$. Define
--   $$
--   D_L(\varepsilon)=\sup\{a\in\mathbb R:\alpha_U(a)\le\varepsilon\},\qquad
--   D_U(\varepsilon)=\sup\{a\in\mathbb R:\alpha_L(a)<\varepsilon\}.
--   $$
--   For every $0\le\varepsilon\le1$,
--   $$
--   B(\varepsilon)=D_L(\varepsilon),\qquad B^\dagger(\varepsilon)=D_U(\varepsilon).
--   $$
--   In particular $B(0)=D_L(0)$, $B^\dagger(1)=D_U(1)$, while $B(1)=+\infty$ and $B^\dagger(0)=-\infty$.
--
--   The theorem identifies the general operational exponents with the information-spectrum divergence rates.
-- source:
--   An Information-Spectrum Approach to Classical and Quantum Hypothesis Testing for Simple Hypotheses, arXiv:quant-ph/0206185v2, PDF p. 7, Theorem 1: general operational exponents equal spectral divergence rates (24)–(27)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46

noncomputable section

open Filter

open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsPositive State relativeEntropy)

universe u

namespace QAlgorithms.Papers.Independent.Claimed50.P46

/-- Theorem 1, PDF p.7, (24)–(27), with both endpoint values noted on p.6. -/
theorem theorem1_spectral_operational (P : ℕ → SimpleHypothesisSystem.{u}) (hP : OriginalNormalization P)
    (S : LikelihoodFamily P) :
    (∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
      steinB P eps = divergenceL S eps ∧ steinBdag P eps = divergenceU S eps) ∧
    steinB P 0 = divergenceL S 0 ∧ steinBdag P 1 = divergenceU S 1 ∧
    steinB P 1 = ⊤ ∧ steinBdag P 0 = ⊥ := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P46

end
