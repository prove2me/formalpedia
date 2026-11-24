-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_card_pos_real_b5d9ffd13cbb
-- name    : P2M_GroundTheory_Heights__Heights_KCoord_card_pos_real_b5d9ffd13cbb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:55.226237+00:00
-- url     : https://prove2.me/theorems/131006ab-6c4c-49dd-b219-e84289f29956
-- title:
--   P2 M Ground Theory Heights  Heights KCoord card pos real b5d9ffd13cbb: P2 M Ground Theory Heights  Heights KCoord card pos real b5d9ffd13cbb
-- statement:
--   The P2 M Ground Theory Heights  Heights KCoord card pos real b5d9ffd13cbb construction uses the P2 M Ground Theory Heights  Heights KCoord card pos real b5d9ffd13cbb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordWeak.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordWeak.lean#L15-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CoordWeak
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
open Real
open GroundTheory.Heights₂.Heights.KCoord
variable {S : Type*} [Fintype S]

theorem P2M_GroundTheory_Heights__Heights_KCoord_card_pos_real_b5d9ffd13cbb [Nonempty S] : (0 : ℝ) < Fintype.card S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KCoord».«card_pos_real» := P2M_GroundTheory_Heights__Heights_KCoord_card_pos_real_b5d9ffd13cbb
