-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P42_criticalBranch_trigonometricEstimates
-- name    : QAlgorithms.Papers.Independent.Renew46.P42.criticalBranch_trigonometricEstimates
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:36:22.934749+00:00
-- url     : https://prove2.me/theorems/1cd3838d-2ad6-4e9b-95b3-6f4326e36f31
-- title:
--   Auxiliary trigonometric estimates
-- statement:
--   For real $x$, the following two inequalities hold on their indicated intervals:
--
--   $$\arccos x\ge\pi-\frac\pi2\sqrt{1+x}\quad(-1\le x\le0),\qquad\cos x\ge\frac3\pi x-\frac92\quad(\pi/2\le x\le\pi).$$
--
--   These are the explicit auxiliary estimates used in the source's discussion of the physical critical branch.
-- source:
--   Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, PDF p. 10, §IV D, (97): auxiliary inequalities used for the physical branch

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.10, (97): the two auxiliary real trigonometric estimates, with
exactly the printed intervals and constants. -/
theorem criticalBranch_trigonometricEstimates :
    (∀ x : ℝ, -1 ≤ x → x ≤ 0 →
      Real.arccos x ≥ -(1 / 2 : ℝ) * Real.sqrt (1 + x) * Real.pi + Real.pi) ∧
    (∀ x : ℝ, Real.pi / 2 ≤ x → x ≤ Real.pi →
      Real.cos x ≥ (3 / Real.pi) * x - (9 / 2 : ℝ)) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P42
