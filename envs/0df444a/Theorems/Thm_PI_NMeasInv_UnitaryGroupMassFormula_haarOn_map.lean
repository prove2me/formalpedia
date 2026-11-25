-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_haarOn_map
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.haarOn_map
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:15:54.149939+00:00
-- url     : https://prove2.me/theorems/06a77f71-1d12-517f-9bdc-2be022a01a0d
-- title:
--   Unitary Group Mass Formula: haar On map
-- statement:
--   The Unitary Group Mass Formula construction uses the haar On map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/RightInvOfContract.lean#L171-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/RightInvOfContract.lean#L171-L188

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

theorem PI.NMeasInv.UnitaryGroupMassFormula.haarOn_map (N : Subgroup G) (hN : IsClosed (N : Set G)) {μ : Measure G} (hμ : HaarOn N μ)
    (φ : G → G) (e : G ≃ₜ G) (he : ⇑e = φ) (hNφ : ∀ x ∈ N, φ x ∈ N)
    (hl : ∀ s ∈ N, ∃ s' ∈ N, ∀ x, s * φ x = φ (s' * x)) : HaarOn N (μ.map φ) := by sorry
