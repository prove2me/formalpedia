-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isReduced_tensorProduct_field_of_perfectField_9cfa4a0469a9
-- name    : P2M_GroundTheory_Heights__Heights_isReduced_tensorProduct_field_of_perfectField_9cfa4a0469a9
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:06.747401+00:00
-- url     : https://prove2.me/theorems/6601b0d9-f2b6-5dd9-a053-7565f6b7af4d
-- title:
--   P2 M Ground Theory Heights  Heights is Reduced tensor Product field of perfect Field 9cfa4a0469a9: P2 M Ground Theory Heights  Heights is Reduced tensor Product field of perfect Field 9cfa4a0469a9
-- statement:
--   The P2 M Ground Theory Heights  Heights is Reduced tensor Product field of perfect Field 9cfa4a0469a9 construction uses the P2 M Ground Theory Heights  Heights is Reduced tensor Product field of perfect Field 9cfa4a0469a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ReducedTensorPerfect.lean#L79-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ReducedTensorPerfect.lean#L79-L96

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
set_option synthInstance.maxHeartbeats 400000

theorem P2M_GroundTheory_Heights__Heights_isReduced_tensorProduct_field_of_perfectField_9cfa4a0469a9 (K : Type u) [Field K] [PerfectField K]
    (L : Type u) [Field L] [Algebra K L] (E : Type u) [Field E] [Algebra K E]
    [Algebra.EssFiniteType K E] : IsReduced (L ⊗[K] E) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isReduced_tensorProduct_field_of_perfectField» := P2M_GroundTheory_Heights__Heights_isReduced_tensorProduct_field_of_perfectField_9cfa4a0469a9
