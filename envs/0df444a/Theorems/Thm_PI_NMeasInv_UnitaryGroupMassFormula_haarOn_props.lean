-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_haarOn_props
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.haarOn_props
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:07:35.037784+00:00
-- url     : https://prove2.me/theorems/5708f05c-ca29-4ec2-8fc8-566187d864a5
-- title:
--   Unitary Group Mass Formula: haar On props
-- statement:
--   The Unitary Group Mass Formula construction uses the haar On props property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/RightInvOfContract.lean#L76-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/RightInvOfContract.lean#L76-L103

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

theorem PI.NMeasInv.UnitaryGroupMassFormula.haarOn_props (H : Subgroup G) (hH : IsClosed (H : Set G)) (μ : Measure G) (hμ : HaarOn H μ) :
    (∀ K : Set G, IsCompact K → μ K < ⊤) ∧
      ∀ U : Set G, IsOpen U → (U ∩ (H : Set G)).Nonempty → 0 < μ U := by sorry
