-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_cxHessian_add_re
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.cxHessian_add_re
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:47.431307+00:00
-- url     : https://prove2.me/theorems/3e624860-c780-4cf5-8aff-da10f180daf7
-- title:
--   Geo: cx Hessian add re
-- statement:
--   The Geo construction uses the cx Hessian add re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterSheetA.lean#L111-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterSheetA.lean#L111-L147

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.cxHessian_add_re {φ : (Fin e → ℂ) → ℝ} {G : (Fin e → ℂ) → ℂ} {y : Fin e → ℂ} (C : ℝ)
    (hφ : ContDiffAt ℝ 2 φ y) (hG : AnalyticAt ℂ G y) :
    cxHessian (fun y' => φ y' + (G y').re + C) y = cxHessian φ y := by sorry
