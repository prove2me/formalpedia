-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_X_cd
-- name    : ReciprocityTheory.ChartRestriction.DS.slm_X_cd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:12:50.815543+00:00
-- url     : https://prove2.me/theorems/51179a78-35e2-4f47-9a3d-3e30b9013955
-- title:
--   DS: slm X cd
-- statement:
--   The DS construction uses the slm X cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CayleyChartDomainIsOpen.lean#L254-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CayleyChartDomainIsOpen.lean#L254-L263

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
local notation "JJ" => Formalism.REAL.Jm

theorem ReciprocityTheory.ChartRestriction.DS.slm_X_cd (ε : Fin n → Bool) (g0 : Matrix (Fin n) (Fin n) ℂ) :
    ContDiffOn ℝ ∞ (slmX ε g0) (cayleyChartDomain ε g0) := by sorry
