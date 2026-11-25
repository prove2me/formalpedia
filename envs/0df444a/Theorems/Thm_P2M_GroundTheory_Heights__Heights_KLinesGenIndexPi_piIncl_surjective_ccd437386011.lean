-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesGenIndexPi_piIncl_surjective_ccd437386011
-- name    : P2M_GroundTheory_Heights__Heights_KLinesGenIndexPi_piIncl_surjective_ccd437386011
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:39.861834+00:00
-- url     : https://prove2.me/theorems/fee10334-849f-48dd-8610-58652b5e133d
-- title:
--   P2 M Ground Theory Heights  Heights KLines Gen Index Pi pi Incl surjective ccd437386011: P2 M Ground Theory Heights  Heights KLines Gen Index Pi pi Incl surjective ccd437386011
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Gen Index Pi pi Incl surjective ccd437386011 construction uses the P2 M Ground Theory Heights  Heights KLines Gen Index Pi pi Incl surjective ccd437386011 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesGenIndexPi.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesGenIndexPi.lean#L26-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGenIndexPi
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
open GroundTheory.Heights₂.Heights.KLinesGenIndexPi
open AddSubgroup
variable {η : Type} {G : Type} [AddCommGroup G]

theorem P2M_GroundTheory_Heights__Heights_KLinesGenIndexPi_piIncl_surjective_ccd437386011 (K : η → AddSubgroup G) : Function.Surjective (piIncl K) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesGenIndexPi».«piIncl_surjective» := P2M_GroundTheory_Heights__Heights_KLinesGenIndexPi_piIncl_surjective_ccd437386011
