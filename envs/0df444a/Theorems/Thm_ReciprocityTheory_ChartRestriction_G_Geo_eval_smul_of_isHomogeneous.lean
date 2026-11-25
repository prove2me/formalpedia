-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_smul_of_isHomogeneous
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.eval_smul_of_isHomogeneous
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:24:11.212101+00:00
-- url     : https://prove2.me/theorems/2f41338e-da3d-5bac-affa-a6f9b663cc64
-- title:
--   Geo: eval smul of is Homogeneous
-- statement:
--   The Geo construction uses the eval smul of is Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeO.lean#L17-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeO.lean#L17-L30

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeJ
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeO
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
open MvPolynomial MeasureTheory

theorem ReciprocityTheory.ChartRestriction.G.Geo.eval_smul_of_isHomogeneous {n : ℕ} {c : MvPolynomial (Fin n) ℂ} {m : ℕ}
    (hc : c.IsHomogeneous m) (t : ℂ) (v : Fin n → ℂ) :
    eval (fun i => t * v i) c = t ^ m * eval v c := by sorry
