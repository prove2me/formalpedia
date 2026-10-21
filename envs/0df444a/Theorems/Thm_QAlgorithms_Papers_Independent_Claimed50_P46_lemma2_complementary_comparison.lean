-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P46_lemma2_complementary_comparison
-- name    : QAlgorithms.Papers.Independent.Claimed50.P46.lemma2_complementary_comparison
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:23:37.770993+00:00
-- url     : https://prove2.me/theorems/7201bd5d-f510-48e0-b3a8-65567c2c5215
-- title:
--   Lemma 2: complementary correct-testing exponent comparison (55)–(56)
-- statement:
--   Work in the classical or quantum testing model on finite or countable alphabets or arbitrary complex Hilbert spaces, respectively, with the normalization $0<\rho_n[I]\le\infty$, $\sigma_n[I]=1$. Classical weights are pointwise finite and quantum weights are bounded positive operators. All effects are permitted as tests. Define $\alpha_n[T_n]=\rho_n[I-T_n]$ and $\beta_n[T_n]=\sigma_n[T_n]$. Write $\eta_L,\eta_U$ for the liminf and limsup of $-\log\alpha_n/n$, and $\zeta_L^c,\zeta_U^c$ for the liminf and limsup of $-\log\sigma_n[I-T_n]/n$. These are extended real values with natural logarithms. Choose any likelihood family $S_n(a)$ allowed by (6), including any effect on the zero subspace. An exponent evaluated at $a$ refers to this family; tests in operational optimizations range independently over all test sequences.
--
--   For every real $a$ and every test sequence $T$,
--   $$
--   \zeta_U^c[T]\ge\min\{\zeta_U^c(a),a+\eta_L[T]\}.
--   $$
--   If $a<b$ and $\zeta_U^c(a)>\zeta_U^c(b)$, then
--   $$
--   \zeta_U^c(b)\ge a+\eta_L(b).
--   $$
--
--   This is the complementary comparison in the switched normalization.
-- source:
--   An Information-Spectrum Approach to Classical and Quantum Hypothesis Testing for Simple Hypotheses, arXiv:quant-ph/0206185v2, PDF p. 13, Lemma 2: complementary correct-testing exponent comparison (55)–(56)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46

noncomputable section

open Filter

open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsPositive State relativeEntropy)

universe u

namespace QAlgorithms.Papers.Independent.Claimed50.P46

/-- Lemma 2, PDF p.13, (55)–(56), under switched normalization (54). -/
theorem lemma2_complementary_comparison (P : ℕ → SimpleHypothesisSystem.{u}) (hP : SwitchedNormalization P)
    (S : LikelihoodFamily P) :
    (∀ (a : ℝ) (T : (k : ℕ) → SimpleHypothesisTest (P k)),
      min (zetaUc (S.tests a)) ((a : EReal) + etaL T) ≤ zetaUc T) ∧
    (∀ a b : ℝ, a < b → zetaUc (S.tests b) < zetaUc (S.tests a) →
      (a : EReal) + etaL (S.tests b) ≤ zetaUc (S.tests b)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P46

end
