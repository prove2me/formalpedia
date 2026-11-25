-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_haarOn_unique
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.haarOn_unique
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:09:48.434807+00:00
-- url     : https://prove2.me/theorems/95031655-e340-4373-ad81-49762d4a96df
-- title:
--   Unitary Group Mass Formula: haar On unique
-- statement:
--   The Unitary Group Mass Formula construction uses the haar On unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/RightInvOfContract.lean#L145-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/RightInvOfContract.lean#L145-L154

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

theorem PI.NMeasInv.UnitaryGroupMassFormula.haarOn_unique (N : Subgroup G) (hN : IsClosed (N : Set G)) {μ ν : Measure G} (hμ : HaarOn N μ)
    (hν : HaarOn N ν) : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ν = c • μ := by sorry
