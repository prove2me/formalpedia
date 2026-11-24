-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_index_ne_zero_0c8323a65fb2
-- name    : P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_index_ne_zero_0c8323a65fb2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:20.319794+00:00
-- url     : https://prove2.me/theorems/66a0121f-0fff-41af-9f82-3d1b3bf2aa8b
-- title:
--   P2 M Ground Theory Heights  Heights Targets Invertible Index Multiplicative index ne zero 0c8323a65fb2: P2 M Ground Theory Heights  Heights Targets Invertible Index Multiplicative index ne zero 0c8323
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Invertible Index Multiplicative index ne zero 0c8323a65fb2 construction uses the P2 M Ground Theory Heights  Heights Targets Invertible Index Multiplicative index ne zero 0c8323a65fb2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PInvertibleIndexMul.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PInvertibleIndexMul.lean#L17-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMulSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PInvertibleIdealIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_POrderIdealIndexExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PInvertibleIndexMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open GroundTheory.Heights₂.Heights InvertibleIdealIndexAlt
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.InvertibleIndexMultiplicative
variable {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_index_ne_zero_0c8323a65fb2 [CharZero Ω] {B : Subring Ω} [Module.Finite ℤ B] {I : Ideal B} (hI : I ≠ ⊥) :
    I.toAddSubgroup.index ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«InvertibleIndexMultiplicative».«index_ne_zero» := P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_index_ne_zero_0c8323a65fb2
