-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_finMean_mono_a9bc735337a8
-- name    : P2M_GroundTheory_Heights__Heights_KCoord_finMean_mono_a9bc735337a8
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:25:33.605018+00:00
-- url     : https://prove2.me/theorems/8744add2-d6d6-468b-84b6-d7fce983c45a
-- title:
--   P2 M Ground Theory Heights  Heights KCoord fin Mean mono a9bc735337a8: P2 M Ground Theory Heights  Heights KCoord fin Mean mono a9bc735337a8
-- statement:
--   The P2 M Ground Theory Heights  Heights KCoord fin Mean mono a9bc735337a8 construction uses the P2 M Ground Theory Heights  Heights KCoord fin Mean mono a9bc735337a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordWeak.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordWeak.lean#L18-L19

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

theorem P2M_GroundTheory_Heights__Heights_KCoord_finMean_mono_a9bc735337a8 [Nonempty S] {f h : S → ℝ} (hfh : ∀ s, f s ≤ h s) : finMean f ≤ finMean h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KCoord».«finMean_mono» := P2M_GroundTheory_Heights__Heights_KCoord_finMean_mono_a9bc735337a8
