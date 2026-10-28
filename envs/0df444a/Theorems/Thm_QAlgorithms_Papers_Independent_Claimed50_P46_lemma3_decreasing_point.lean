-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P46_lemma3_decreasing_point
-- name    : QAlgorithms.Papers.Independent.Claimed50.P46.lemma3_decreasing_point
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:25:26.405385+00:00
-- url     : https://prove2.me/theorems/82a9bbf0-f14e-4fd8-b9b7-a8be7465bd03
-- title:
--   Lemma 3: spectral upper exponent and decreasing-point limit (76)–(77)
-- statement:
--   Work in the classical or quantum testing model on finite or countable alphabets or arbitrary complex Hilbert spaces, respectively, with the normalization $0<\rho_n[I]\le\infty$, $\sigma_n[I]=1$. Classical weights are pointwise finite and quantum weights are bounded positive operators. All effects are permitted as tests. Define $\alpha_n[T_n]=\rho_n[I-T_n]$ and $\beta_n[T_n]=\sigma_n[T_n]$. Write $\eta_L,\eta_U$ for the liminf and limsup of $-\log\alpha_n/n$, and $\zeta_L^c,\zeta_U^c$ for the liminf and limsup of $-\log\sigma_n[I-T_n]/n$. These are extended real values with natural logarithms. Choose any likelihood family $S_n(a)$ allowed by (6), including any effect on the zero subspace. An exponent evaluated at $a$ refers to this family; tests in operational optimizations range independently over all test sequences.
--
--   For every real $a$,
--   $$
--   \zeta_U^c(a)\le a+\eta_U(a).
--   $$
--   If $\zeta_U^c(a-\varepsilon)>\zeta_U^c(a+\varepsilon)$ for every $\varepsilon>0$, then
--   $$
--   \zeta_U^c(a+0)\ge a+\eta_L(a+0).
--   $$
--   Right limits are those of the corresponding nonincreasing functions.
--
--   The upper exponent in the first clause and lower exponent in the second remain distinct.
-- source:
--   An Information-Spectrum Approach to Classical and Quantum Hypothesis Testing for Simple Hypotheses, arXiv:quant-ph/0206185v2, PDF p. 15, Lemma 3: spectral upper exponent and decreasing-point limit (76)–(77)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46

noncomputable section

open Filter

open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsPositive State relativeEntropy)

universe u

namespace QAlgorithms.Papers.Independent.Claimed50.P46

/-- Lemma 3, PDF p.15: (76) uses etaU, whereas (77) uses etaL at a decreasing point. -/
theorem lemma3_decreasing_point (P : ℕ → SimpleHypothesisSystem.{u}) (hP : SwitchedNormalization P)
    (S : LikelihoodFamily P) (a : ℝ) :
    zetaUc (S.tests a) ≤ (a : EReal) + etaU (S.tests a) ∧
    ((∀ e : ℝ, 0 < e → zetaUc (S.tests (a + e)) < zetaUc (S.tests (a - e))) →
      (a : EReal) + decreasingRight (fun b => etaL (S.tests b)) a ≤
        decreasingRight (fun b => zetaUc (S.tests b)) a) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P46

end
