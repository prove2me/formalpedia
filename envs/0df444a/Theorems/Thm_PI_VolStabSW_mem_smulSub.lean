-- Prove2me | Theorems.Thm_PI_VolStabSW_mem_smulSub
-- name    : PI.VolStabSW.mem_smulSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:46.7749+00:00
-- url     : https://prove2.me/theorems/ff685dbe-9b85-4bde-94d4-2e409df72db9
-- title:
--   Vol Stab SW: mem smul Sub
-- statement:
--   The Vol Stab SW construction uses the mem smul Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/EventuallySmulSub.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/EventuallySmulSub.lean#L20-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_MeasureEqOfCos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_EventuallySmulSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open Topology Filter Set
variable {K V X : Type} [Field K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V]
  [AddCommGroup X] [Module K X] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul K X]
omit [TopologicalSpace K]

theorem PI.VolStabSW.mem_smulSub {W : Type} [AddCommGroup W] [Module K W] (t : K) (P : AddSubgroup W) (z : W) :
    z ∈ smulSub t P ↔ ∃ p ∈ P, t • p = z := by sorry
