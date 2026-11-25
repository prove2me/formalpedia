-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootsOfUnityDenseAlt_rootsOfUnity_infinite_fb3881bcacd7
-- name    : P2M_GroundTheory_Heights__Heights_RootsOfUnityDenseAlt_rootsOfUnity_infinite_fb3881bcacd7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:36:43.33924+00:00
-- url     : https://prove2.me/theorems/ac8ca840-bf0c-4298-b3ac-8b64253a29c6
-- title:
--   P2 M Ground Theory Heights  Heights Roots Of Unity Dense Alt roots Of Unity infinite fb3881bcacd7: P2 M Ground Theory Heights  Heights Roots Of Unity Dense Alt roots Of Unity infinite fb3881bcacd7
-- statement:
--   The P2 M Ground Theory Heights  Heights Roots Of Unity Dense Alt roots Of Unity infinite fb3881bcacd7 construction uses the P2 M Ground Theory Heights  Heights Roots Of Unity Dense Alt roots Of Unity infinite fb3881bcacd7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootsOfUnityDense.lean#L11-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootsOfUnityDense.lean#L11-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootsOfUnityDense
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
open GroundTheory.Heights₂.Heights.RootsOfUnityDenseAlt
open Complex

theorem P2M_GroundTheory_Heights__Heights_RootsOfUnityDenseAlt_rootsOfUnity_infinite_fb3881bcacd7 :
    {z : ℂ | ∃ k : ℕ, 0 < k ∧ z ^ k = 1}.Infinite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootsOfUnityDenseAlt».«rootsOfUnity_infinite» := P2M_GroundTheory_Heights__Heights_RootsOfUnityDenseAlt_rootsOfUnity_infinite_fb3881bcacd7
