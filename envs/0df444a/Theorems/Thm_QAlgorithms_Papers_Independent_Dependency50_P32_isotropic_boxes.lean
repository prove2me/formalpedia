-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P32_isotropic_boxes
-- name    : QAlgorithms.Papers.Independent.Dependency50.P32.isotropic_boxes
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:03:32.416794+00:00
-- url     : https://prove2.me/theorems/3efd8652-7fb7-43a0-b24d-4dfab698fe6e
-- title:
--   PR endpoint monotones and isotropic no-distillation
-- statement:
--   In the binary Bell scenario let $B_p=(1-p)B_{\rm PR}+pB_{\rm random}$, with white-noise probabilities $1/4$. All no-signalling classical channels are allowed; local shared-randomness boxes are free. Resource quantities are multiplicative generalized robustness, standard robustness, and ordinary min-resource relative to this local fibre. Then
--   $$R_{\max}(B_{\rm PR})=R_{\min}(B_{\rm PR})=\frac43,\qquad R_s(B_{\rm PR})=\frac32.$$
--   For every $0<p\le1$ and every positive finite integer $n$,
--   $$R_{\min}(B_p^{\otimes n})=1,\qquad B_p^{\otimes n}\not\longrightarrow B_{\rm PR}\ \text{exactly by a physical free superchannel}.$$
--   The transformation family is the maximal deterministic family preserving allowed boxes and local boxes; collective registers are grouped by party.
--
--   Only the analytically stated endpoint values and finite-copy impossibility are asserted. No visually fitted line-segment formula from the numerical plot is promoted to a theorem.
-- source:
--   One-Shot Manipulation of Dynamical Quantum Resources, arXiv:2012.02215v3, PDF p. 14, PR endpoint monotones and isotropic no-distillation

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms.Papers.Independent.Information100.P07 (support)

/-- Appendix F and Fig.1, PDF pp.14-15: exact PR endpoint values 4/3 and 3/2,
and finite-copy isotropic no-distillation for 0<p<=1. The plotted line segments
are numerical evaluations and are not promoted to analytic formulas here. -/
theorem isotropic_boxes :
    maximal boxTheory (boxChoi binarySplit prKernel) = ENNReal.ofReal (4 / 3 : ℝ) ∧
    standard boxTheory (boxChoi binarySplit prKernel) = ENNReal.ofReal (3 / 2 : ℝ) ∧
    minimum boxTheory (boxChoi binarySplit prKernel) = ENNReal.ofReal (4 / 3 : ℝ) ∧
    ∀ p : ℝ, 0 < p → p ≤ 1 → ∀ n : ℕ, 0 < n →
      let B := boxChoi (copySplit n) (tensorKernel n (isotropicKernel p))
      minimum boxTheory B = 1 ∧ ¬ Converts boxTheory B (boxChoi binarySplit prKernel) 0 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P32

end
