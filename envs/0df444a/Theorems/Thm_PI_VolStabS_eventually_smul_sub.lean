-- Prove2me | Theorems.Thm_PI_VolStabS_eventually_smul_sub
-- name    : PI.VolStabS.eventually_smul_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:28:46.666798+00:00
-- url     : https://prove2.me/theorems/b84a3491-1944-4faa-a94c-f68087eef7b1
-- title:
--   Vol Stab S: eventually smul sub
-- statement:
--   The Vol Stab S construction uses the eventually smul sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/EventuallySmulSub.lean#L41-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/EventuallySmulSub.lean#L41-L51

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_MeasureEqOfCos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_EventuallySmulSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open Topology Filter Set
variable {K V X : Type} [Field K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V]
  [AddCommGroup X] [Module K X] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul K X]

theorem PI.VolStabS.eventually_smul_sub {W : Type} [AddCommGroup W] [Module K W] [TopologicalSpace W]
    [ContinuousSMul K W] (S : Set W) (hS : IsCompact S) (s : ℕ → K)
    (hs : Tendsto s atTop (𝓝 0)) (N : Set W) (hN : N ∈ 𝓝 (0 : W)) :
    ∃ k, ∀ p ∈ S, s k • p ∈ N := by sorry
