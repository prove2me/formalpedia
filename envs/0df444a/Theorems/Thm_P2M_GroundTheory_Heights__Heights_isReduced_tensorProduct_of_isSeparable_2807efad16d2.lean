-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isReduced_tensorProduct_of_isSeparable_2807efad16d2
-- name    : P2M_GroundTheory_Heights__Heights_isReduced_tensorProduct_of_isSeparable_2807efad16d2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:17.593548+00:00
-- url     : https://prove2.me/theorems/395291b3-68e9-4e62-a617-df7b937f79ef
-- title:
--   P2 M Ground Theory Heights  Heights is Reduced tensor Product of is Separable 2807efad16d2: P2 M Ground Theory Heights  Heights is Reduced tensor Product of is Separable 2807efad16d2
-- statement:
--   The P2 M Ground Theory Heights  Heights is Reduced tensor Product of is Separable 2807efad16d2 construction uses the P2 M Ground Theory Heights  Heights is Reduced tensor Product of is Separable 2807efad16d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ReducedTensorPerfect.lean#L51-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ReducedTensorPerfect.lean#L51-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ReducedTensorPerfect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open TensorProduct
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_isReduced_tensorProduct_of_isSeparable_2807efad16d2 {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Algebra.IsSeparable F E] [Algebra.EssFiniteType F E]
    (D : Type u) [CommRing D] [Algebra F D] [IsReduced D] : IsReduced (E ⊗[F] D) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isReduced_tensorProduct_of_isSeparable» := P2M_GroundTheory_Heights__Heights_isReduced_tensorProduct_of_isSeparable_2807efad16d2
