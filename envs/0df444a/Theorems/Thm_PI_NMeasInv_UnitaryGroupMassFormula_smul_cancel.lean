-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_smul_cancel
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.smul_cancel
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:16:07.96552+00:00
-- url     : https://prove2.me/theorems/4356f54e-1c88-4086-ab2a-5cccf6333e6f
-- title:
--   Unitary Group Mass Formula: smul cancel
-- statement:
--   The Unitary Group Mass Formula construction uses the smul cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/RightInvOfContract.lean#L164-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/RightInvOfContract.lean#L164-L169

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

theorem PI.NMeasInv.UnitaryGroupMassFormula.smul_cancel {μ : Measure G} {K : Set G} (hK0 : 0 < μ K) (hKt : μ K < ⊤) {c d : ℝ≥0∞}
    (h : c • μ = d • μ) : c = d := by sorry
