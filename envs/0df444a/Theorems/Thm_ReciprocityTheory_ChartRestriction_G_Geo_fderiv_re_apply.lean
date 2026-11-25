-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fderiv_re_apply
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.fderiv_re_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:24:16.585704+00:00
-- url     : https://prove2.me/theorems/8ae7a34c-83bd-4359-b7ce-fbde4104d249
-- title:
--   Geo: fderiv re apply
-- statement:
--   The Geo construction uses the fderiv re apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterSheetA.lean#L85-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterSheetA.lean#L85-L91

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial Filter Topology
variable {e : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Geo.fderiv_re_apply {h : (Fin e → ℂ) → ℂ} {y : Fin e → ℂ} (hh : DifferentiableAt ℂ h y)
    (v : Fin e → ℂ) : fderiv ℝ (fun y' => (h y').re) y v = (fderiv ℂ h y v).re := by sorry
