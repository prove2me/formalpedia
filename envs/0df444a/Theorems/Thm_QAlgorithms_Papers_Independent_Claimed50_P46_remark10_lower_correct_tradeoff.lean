-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P46_remark10_lower_correct_tradeoff
-- name    : QAlgorithms.Papers.Independent.Claimed50.P46.remark10_lower_correct_tradeoff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:24:51.096372+00:00
-- url     : https://prove2.me/theorems/0b8a0f11-0b39-45da-91d7-eb1adb09ded6
-- title:
--   Remark 10: lower-limit correct-testing analogue (68)–(75)
-- statement:
--   Work in the classical or quantum testing model on finite or countable alphabets or arbitrary complex Hilbert spaces, respectively, with the normalization $0<\rho_n[I]\le\infty$, $\sigma_n[I]=1$. Classical weights are pointwise finite and quantum weights are bounded positive operators. All effects are permitted as tests. Define $\alpha_n[T_n]=\rho_n[I-T_n]$ and $\beta_n[T_n]=\sigma_n[T_n]$. Write $\eta_L,\eta_U$ for the liminf and limsup of $-\log\alpha_n/n$, and $\zeta_L^c,\zeta_U^c$ for the liminf and limsup of $-\log\sigma_n[I-T_n]/n$. These are extended real values with natural logarithms. Choose any likelihood family $S_n(a)$ allowed by (6), including any effect on the zero subspace. An exponent evaluated at $a$ refers to this family; tests in operational optimizations range independently over all test sequences.
--
--   For every $a,T$,
--   $$
--   \zeta_L^c[T]\ge\min\{\zeta_L^c(a),a+\eta_L[T]\}.
--   $$
--   Define $\widehat B_e^*,\widehat B_{e,1}^*$ using the lower complementary exponent, with the asymptotic and every-block type-I constraints, respectively. For every real $r$,
--   $$
--   \widehat B_e^*(r)=\widehat B_{e,1}^*(r)=\sup_a\min\{\zeta_L^c(a),r+a\}
--   =\inf_a\max\{\zeta_L^c(a),r+a\}=r+\widehat a_0^*,
--   $$
--   where $\widehat a_0^*=\sup\{a:\zeta_L^c(a)\ge r+a\}=\inf\{a:\zeta_L^c(a)\le r+a\}$.
--
--   This is the separate lower-limit correct-testing analogue, including its comparison inequality.
-- source:
--   An Information-Spectrum Approach to Classical and Quantum Hypothesis Testing for Simple Hypotheses, arXiv:quant-ph/0206185v2, PDF p. 15, Remark 10: lower-limit correct-testing analogue (68)–(75)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46

noncomputable section

open Filter

open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsPositive State relativeEntropy)

universe u

namespace QAlgorithms.Papers.Independent.Claimed50.P46

/-- Remark 10, PDF p.15, (68)–(75): separate lower-limit objective and spectral exponent. -/
theorem remark10_lower_correct_tradeoff (P : ℕ → SimpleHypothesisSystem.{u}) (hP : SwitchedNormalization P)
    (S : LikelihoodFamily P) :
    (∀ (a : ℝ) (T : (k : ℕ) → SimpleHypothesisTest (P k)),
      min (zetaLc (S.tests a)) ((a : EReal) + etaL T) ≤ zetaLc T) ∧
    (∀ r : ℝ, let f := fun a => zetaLc (S.tests a)
      correctTradeoff P false false r = correctTradeoff P false true r ∧
      correctTradeoff P false false r = (⨆ a : ℝ, min (f a) ((r + a : ℝ) : EReal)) ∧
      correctTradeoff P false false r = (⨅ a : ℝ, max (f a) ((r + a : ℝ) : EReal)) ∧
      correctTradeoff P false false r = (r : EReal) + correctCutoff f r ∧
      correctCutoff f r = sInf {z | ∃ a : ℝ, f a ≤ ((r + a : ℝ) : EReal) ∧ z = (a : EReal)}) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P46

end
