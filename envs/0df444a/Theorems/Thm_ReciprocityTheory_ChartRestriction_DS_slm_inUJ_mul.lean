-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_inUJ_mul
-- name    : ReciprocityTheory.ChartRestriction.DS.slm_inUJ_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:17:56.731205+00:00
-- url     : https://prove2.me/theorems/c1aae43f-70c3-4379-b22b-69f990fddb71
-- title:
--   DS: slm in UJ mul
-- statement:
--   The DS construction uses the slm in UJ mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CayleyChartDomainIsOpen.lean#L125-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CayleyChartDomainIsOpen.lean#L125-L130

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

theorem ReciprocityTheory.ChartRestriction.DS.slm_inUJ_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : Formalism.REAL.inUJ ε a)
    (hb : Formalism.REAL.inUJ ε b) : Formalism.REAL.inUJ ε (a * b) := by sorry
