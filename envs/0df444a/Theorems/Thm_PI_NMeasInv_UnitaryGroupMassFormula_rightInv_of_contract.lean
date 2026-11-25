-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_rightInv_of_contract
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.rightInv_of_contract
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:14:16.119345+00:00
-- url     : https://prove2.me/theorems/4d5e632b-b4e1-4575-b905-b740a4e90dcc
-- title:
--   Unitary Group Mass Formula: right Inv of contract
-- statement:
--   The Unitary Group Mass Formula construction uses the right Inv of contract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/RightInvOfContract.lean#L214-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/RightInvOfContract.lean#L214-L300

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

theorem PI.NMeasInv.UnitaryGroupMassFormula.rightInv_of_contract (N : Subgroup G) (hN : IsClosed (N : Set G)) {μ : Measure G} (hμ : HaarOn N μ)
    (C : Set G) (hC : IsCompact C)
    (hcon : ∀ n ∈ N, ∃ a : G, (∀ x ∈ N, a * x * a⁻¹ ∈ N) ∧ (∀ x ∈ N, a⁻¹ * x * a ∈ N) ∧ a * n * a⁻¹ ∈ C) :
    ∀ n ∈ N, μ.map (fun x => x * n) = μ := by sorry
