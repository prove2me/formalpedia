-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_FlatWeightedEstimates_wdb_eq
-- name    : ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates.wdb_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:30:39.38501+00:00
-- url     : https://prove2.me/theorems/cf6c07f0-51d3-428b-8a17-69fb4d8e97bd
-- title:
--   Flat Weighted Estimates: wdb eq
-- statement:
--   The Flat Weighted Estimates construction uses the wdb eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/IntegrableFd.lean#L59-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/IntegrableFd.lean#L59-L62

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollifierL2LocTendsto
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableFd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
open ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates

theorem ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates.wdb_eq (n : ℕ) (j : Fin n) (φ : V n → ℂ) (y : V n) :
    wdb n j φ y = 1 / 2 * fderiv ℝ φ y (bas n j) + (Complex.I / 2) *
      fderiv ℝ φ y (Complex.I • bas n j) := by sorry
