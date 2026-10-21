-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P46_remark12_saturation
-- name    : QAlgorithms.Papers.Independent.Claimed50.P46.remark12_saturation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:27:17.418873+00:00
-- url     : https://prove2.me/theorems/07ef4bbb-1a35-4105-9fd3-96f563a79aa4
-- title:
--   Remark 12: saturation outside Han's validity range
-- statement:
--   Work in the classical or quantum testing model on finite or countable alphabets or arbitrary complex Hilbert spaces, respectively, with the normalization $0<\rho_n[I]\le\infty$, $\sigma_n[I]=1$. Classical weights are pointwise finite and quantum weights are bounded positive operators. All effects are permitted as tests. Define $\alpha_n[T_n]=\rho_n[I-T_n]$ and $\beta_n[T_n]=\sigma_n[T_n]$. Write $\eta_L,\eta_U$ for the liminf and limsup of $-\log\alpha_n/n$, and $\zeta_L^c,\zeta_U^c$ for the liminf and limsup of $-\log\sigma_n[I-T_n]/n$. These are extended real values with natural logarithms. Choose any likelihood family $S_n(a)$ allowed by (6), including any effect on the zero subspace. An exponent evaluated at $a$ refers to this family; tests in operational optimizations range independently over all test sequences.
--
--   Let $M=\sup_a\zeta_U^c(a)$ and $K=\inf_{a:\zeta_U^c(a)=M}(M-a)$. For any real $r>K$,
--   $$
--   B_e^*(r)=M,\qquad B_e^*(r)=\inf\{\zeta_U^c[T]:\eta_L[T]\ge r\}.
--   $$
--
--   This is the explicit saturation outside the plateau validity range.
-- source:
--   An Information-Spectrum Approach to Classical and Quantum Hypothesis Testing for Simple Hypotheses, arXiv:quant-ph/0206185v2, PDF p. 16, Remark 12: saturation outside Han's validity range

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46

noncomputable section

open Filter

open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsPositive State relativeEntropy)

universe u

namespace QAlgorithms.Papers.Independent.Claimed50.P46

/-- Remark 12, PDF p.16: explicit saturation outside the plateau range. -/
theorem remark12_saturation (P : ℕ → SimpleHypothesisSystem.{u}) (hP : SwitchedNormalization P)
    (S : LikelihoodFamily P) (r : ℝ)
    (hr : plateauThreshold (fun a => zetaUc (S.tests a)) < (r : EReal)) :
    correctTradeoff P true false r = plateauHeight (fun a => zetaUc (S.tests a)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P46

end
