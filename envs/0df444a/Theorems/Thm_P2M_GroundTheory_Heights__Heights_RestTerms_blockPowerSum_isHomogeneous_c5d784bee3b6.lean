-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_blockPowerSum_isHomogeneous_c5d784bee3b6
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_blockPowerSum_isHomogeneous_c5d784bee3b6
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:35:58.085344+00:00
-- url     : https://prove2.me/theorems/da73c10b-9686-4b45-a06d-519b8ae64c2c
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms block Power Sum is Homogeneous c5d784bee3b6: P2 M Ground Theory Heights  Heights Rest Terms block Power Sum is Homogeneous c5d784bee3b6
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms block Power Sum is Homogeneous c5d784bee3b6 construction uses the P2 M Ground Theory Heights  Heights Rest Terms block Power Sum is Homogeneous c5d784bee3b6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L162-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L162-L164

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHomogeneousComponentMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_blockPowerSum_isHomogeneous_c5d784bee3b6 (f N m : ℕ) (τ : Fin f) :
    (blockPowerSum f N m τ).IsHomogeneous m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«blockPowerSum_isHomogeneous» := P2M_GroundTheory_Heights__Heights_RestTerms_blockPowerSum_isHomogeneous_c5d784bee3b6
