-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_map_comap_subgroup
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.map_comap_subgroup
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:15:59.447971+00:00
-- url     : https://prove2.me/theorems/88f791b7-69a8-55fc-a39c-144fcc34370f
-- title:
--   Unitary Group Mass Formula: map comap subgroup
-- statement:
--   The Unitary Group Mass Formula construction uses the map comap subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/RightInvOfContract.lean#L20-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/RightInvOfContract.lean#L20-L30

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_RightInvOfContract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Topology
open scoped ENNReal NNReal
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
attribute [local instance] Classical.propDecidable
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem PI.NMeasInv.UnitaryGroupMassFormula.map_comap_subgroup (H : Subgroup G) (hH : IsClosed (H : Set G)) (μ : Measure G)
    (hc : μ (H : Set G)ᶜ = 0) : (μ.comap ((↑) : H → G)).map ((↑) : H → G) = μ := by sorry
