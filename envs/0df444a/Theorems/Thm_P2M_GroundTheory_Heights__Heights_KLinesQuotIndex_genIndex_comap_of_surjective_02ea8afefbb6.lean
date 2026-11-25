-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesQuotIndex_genIndex_comap_of_surjective_02ea8afefbb6
-- name    : P2M_GroundTheory_Heights__Heights_KLinesQuotIndex_genIndex_comap_of_surjective_02ea8afefbb6
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:40.580367+00:00
-- url     : https://prove2.me/theorems/9068c976-ed1a-4be3-9b30-9b3bc6c1bd64
-- title:
--   P2 M Ground Theory Heights  Heights KLines Quot Index gen Index comap of surjective 02ea8afefbb6: P2 M Ground Theory Heights  Heights KLines Quot Index gen Index comap of surjective 02ea8afefbb6
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Quot Index gen Index comap of surjective 02ea8afefbb6 construction uses the P2 M Ground Theory Heights  Heights KLines Quot Index gen Index comap of surjective 02ea8afefbb6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesQuotIndex.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesQuotIndex.lean#L11-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesQuotIndex
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
open NumberField
open GroundTheory.Heights₂.Heights.KLinesQuotIndex

theorem P2M_GroundTheory_Heights__Heights_KLinesQuotIndex_genIndex_comap_of_surjective_02ea8afefbb6 {G G' : Type*} [AddCommGroup G] [AddCommGroup G']
    (f : G →+ G') (hf : Function.Surjective f) (H H' : AddSubgroup G') :
    genIndex (H.comap f) (H'.comap f) = genIndex H H' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesQuotIndex».«genIndex_comap_of_surjective» := P2M_GroundTheory_Heights__Heights_KLinesQuotIndex_genIndex_comap_of_surjective_02ea8afefbb6
