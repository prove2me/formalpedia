-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_hess_re
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.hess_re
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:23:37.223242+00:00
-- url     : https://prove2.me/theorems/388e25ab-7822-4a5a-b1b6-2420a2d4c281
-- title:
--   Geo: hess re
-- statement:
--   The Geo construction uses the hess re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterSheetA.lean#L93-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterSheetA.lean#L93-L109

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.hess_re {G : (Fin e → ℂ) → ℂ} {y : Fin e → ℂ} (hG : AnalyticAt ℂ G y) (v w : Fin e → ℂ) :
    fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y v w = (fderiv ℂ (fderiv ℂ G) y v w).re := by sorry
