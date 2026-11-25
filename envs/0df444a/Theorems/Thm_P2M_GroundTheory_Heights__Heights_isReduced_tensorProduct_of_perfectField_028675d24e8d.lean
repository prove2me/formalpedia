-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isReduced_tensorProduct_of_perfectField_028675d24e8d
-- name    : P2M_GroundTheory_Heights__Heights_isReduced_tensorProduct_of_perfectField_028675d24e8d
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:19.127186+00:00
-- url     : https://prove2.me/theorems/1fe45cd3-1b95-4880-b524-a55249d1159c
-- title:
--   P2 M Ground Theory Heights  Heights is Reduced tensor Product of perfect Field 028675d24e8d: P2 M Ground Theory Heights  Heights is Reduced tensor Product of perfect Field 028675d24e8d
-- statement:
--   The P2 M Ground Theory Heights  Heights is Reduced tensor Product of perfect Field 028675d24e8d construction uses the P2 M Ground Theory Heights  Heights is Reduced tensor Product of perfect Field 028675d24e8d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ReducedTensorPerfect.lean#L98-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ReducedTensorPerfect.lean#L98-L102

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

theorem P2M_GroundTheory_Heights__Heights_isReduced_tensorProduct_of_perfectField_028675d24e8d (K : Type u) [Field K] [PerfectField K]
    (L : Type u) [Field L] [Algebra K L] (A : Type u) [CommRing A] [Algebra K A] [IsReduced A] :
    IsReduced (L ⊗[K] A) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isReduced_tensorProduct_of_perfectField» := P2M_GroundTheory_Heights__Heights_isReduced_tensorProduct_of_perfectField_028675d24e8d
