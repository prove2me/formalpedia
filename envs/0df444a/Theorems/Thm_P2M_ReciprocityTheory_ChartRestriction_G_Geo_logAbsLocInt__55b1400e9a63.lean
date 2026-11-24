-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_logAbsLocInt__55b1400e9a63
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Geo_logAbsLocInt__55b1400e9a63
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:31.293148+00:00
-- url     : https://prove2.me/theorems/15481bc3-87a9-4937-9052-d62b568e0198
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Geo log Abs Loc Int  55b1400e9a63: P2 M Reciprocity Theory Chart Restriction G Geo log Abs Loc Int  55b1400e9a63
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Geo log Abs Loc Int  55b1400e9a63 construction uses the P2 M Reciprocity Theory Chart Restriction G Geo log Abs Loc Int  55b1400e9a63 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeN.lean#L185-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeN.lean#L185-L207

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeN
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
open MeasureTheory Metric Filter Topology Real

theorem P2M_ReciprocityTheory_ChartRestriction_G_Geo_logAbsLocInt__55b1400e9a63 (D : ℕ) (U : Set (Fin D → ℂ)) (f : (Fin D → ℂ) → ℂ) (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) : LocallyIntegrableOn (fun z => Real.log ‖f z‖) U volume := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Geo».«logAbsLocInt'» := P2M_ReciprocityTheory_ChartRestriction_G_Geo_logAbsLocInt__55b1400e9a63
