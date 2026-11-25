-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_exists_K
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.exists_K
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:16:18.981157+00:00
-- url     : https://prove2.me/theorems/d269ba92-bd83-587d-8ac9-03c432bbfb9f
-- title:
--   Unitary Group Mass Formula: exists K
-- statement:
--   The Unitary Group Mass Formula construction uses the exists K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/RightInvOfContract.lean#L156-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/RightInvOfContract.lean#L156-L162

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

theorem PI.NMeasInv.UnitaryGroupMassFormula.exists_K (N : Subgroup G) (hN : IsClosed (N : Set G)) (μ : Measure G) (hμ : HaarOn N μ) :
    ∃ K : Set G, IsCompact K ∧ 0 < μ K ∧ μ K < ⊤ := by sorry
