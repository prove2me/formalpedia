-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_nrm_rt
-- name    : ReciprocityTheory.ChartRestriction.DS.UnitA.nrm_rt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:27.728355+00:00
-- url     : https://prove2.me/theorems/dd4bb485-2a2c-47ee-aadb-92d7afb60fd7
-- title:
--   Unit A: nrm rt
-- statement:
--   The Unit A construction uses the nrm rt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/UnitarizeA.lean#L133-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/UnitarizeA.lean#L133-L137

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_UnitarizeA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.UnitA
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] (μ : Measure G)
variable {μ}
variable [μ.IsMulRightInvariant]

theorem ReciprocityTheory.ChartRestriction.DS.UnitA.nrm_rt {a : G → ℂ} (ha : AEStronglyMeasurable a μ) (g : G) :
    nrm μ (fun x => a (x * g)) = nrm μ a := by sorry
