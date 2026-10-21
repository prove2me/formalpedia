-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P46_theorem4_correct_tradeoff
-- name    : QAlgorithms.Papers.Independent.Claimed50.P46.theorem4_correct_tradeoff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:24:15.045499+00:00
-- url     : https://prove2.me/theorems/41594725-9bae-4fe5-a721-e62e5614065e
-- title:
--   Theorem 4: correct-testing exponent minimax formula (58)–(63)
-- statement:
--   Work in the classical or quantum testing model on finite or countable alphabets or arbitrary complex Hilbert spaces, respectively, with the normalization $0<\rho_n[I]\le\infty$, $\sigma_n[I]=1$. Classical weights are pointwise finite and quantum weights are bounded positive operators. All effects are permitted as tests. Define $\alpha_n[T_n]=\rho_n[I-T_n]$ and $\beta_n[T_n]=\sigma_n[T_n]$. Write $\eta_L,\eta_U$ for the liminf and limsup of $-\log\alpha_n/n$, and $\zeta_L^c,\zeta_U^c$ for the liminf and limsup of $-\log\sigma_n[I-T_n]/n$. These are extended real values with natural logarithms. Choose any likelihood family $S_n(a)$ allowed by (6), including any effect on the zero subspace. An exponent evaluated at $a$ refers to this family; tests in operational optimizations range independently over all test sequences.
--
--   For real $r$, let $B_e^*(r)=\inf\{\zeta_U^c[T]:\eta_L[T]\ge r\}$, and define $B_{e,1}^*(r)$ by requiring the finite-block type-I exponent to be at least $r$ for every block. Then
--   $$
--   B_e^*(r)=B_{e,1}^*(r)=\sup_a\min\{\zeta_U^c(a),r+a\}
--   =\inf_a\max\{\zeta_U^c(a),r+a\}=r+a_0^*,
--   $$
--   where both crossing descriptions agree:
--   $$
--   a_0^*=\sup\{a:\zeta_U^c(a)\ge r+a\}=\inf\{a:\zeta_U^c(a)\le r+a\}.
--   $$
--
--   The theorem identifies infima over all tests; it does not assert their attainment.
-- source:
--   An Information-Spectrum Approach to Classical and Quantum Hypothesis Testing for Simple Hypotheses, arXiv:quant-ph/0206185v2, PDF p. 14, Theorem 4: correct-testing exponent minimax formula (58)–(63)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46

noncomputable section

open Filter

open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsPositive State relativeEntropy)

universe u

namespace QAlgorithms.Papers.Independent.Claimed50.P46

/-- Theorem 4, PDF p.14, (58)–(63): infima, without a claimed attaining sequence. -/
theorem theorem4_correct_tradeoff (P : ℕ → SimpleHypothesisSystem.{u}) (hP : SwitchedNormalization P)
    (S : LikelihoodFamily P) (r : ℝ) :
    let f := fun a => zetaUc (S.tests a)
    correctTradeoff P true false r = correctTradeoff P true true r ∧
    correctTradeoff P true false r = (⨆ a : ℝ, min (f a) ((r + a : ℝ) : EReal)) ∧
    correctTradeoff P true false r = (⨅ a : ℝ, max (f a) ((r + a : ℝ) : EReal)) ∧
    correctTradeoff P true false r = (r : EReal) + correctCutoff f r ∧
    correctCutoff f r = sInf {z | ∃ a : ℝ, f a ≤ ((r + a : ℝ) : EReal) ∧ z = (a : EReal)} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P46

end
