-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_segreDehom_surjective_b59a58e33f95
-- name    : P2M_GroundTheory_Heights__Heights_Targets_segreDehom_surjective_b59a58e33f95
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:54.212837+00:00
-- url     : https://prove2.me/theorems/74c4968d-d59a-4b81-ad30-c40a21612e97
-- title:
--   P2 M Ground Theory Heights  Heights Targets segre Dehom surjective b59a58e33f95: P2 M Ground Theory Heights  Heights Targets segre Dehom surjective b59a58e33f95
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets segre Dehom surjective b59a58e33f95 construction uses the P2 M Ground Theory Heights  Heights Targets segre Dehom surjective b59a58e33f95 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ChartConeObjects.lean#L125-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ChartConeObjects.lean#L125-L128

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartConeComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ChartConeObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
variable {K : Type*} [Fintype K] {ι : K → Type*}
variable [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_Targets_segreDehom_surjective_b59a58e33f95 {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    Function.Surjective (segreDehom σ i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«segreDehom_surjective» := P2M_GroundTheory_Heights__Heights_Targets_segreDehom_surjective_b59a58e33f95
