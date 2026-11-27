-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isCohenMacaulayAt_point_bc8cbda9b5ee
-- name    : P2M_GroundTheory_Heights__Heights_isCohenMacaulayAt_point_bc8cbda9b5ee
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:41:46.253101+00:00
-- url     : https://prove2.me/theorems/475b2a70-9cc4-52ad-9712-8755e0bfb7e4
-- title:
--   P2 M Ground Theory Heights  Heights is Cohen Macaulay At point bc8cbda9b5ee: P2 M Ground Theory Heights  Heights is Cohen Macaulay At point bc8cbda9b5ee
-- statement:
--   The P2 M Ground Theory Heights  Heights is Cohen Macaulay At point bc8cbda9b5ee construction uses the P2 M Ground Theory Heights  Heights is Cohen Macaulay At point bc8cbda9b5ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StTransverseObjects.lean#L32-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StTransverseObjects.lean#L32-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseObjects
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
open MvPolynomial Matrix ComplexSets IsLocalRing
noncomputable section
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_isCohenMacaulayAt_point_bc8cbda9b5ee (q : Fin n → ℂ) :
    IsCohenMacaulayAt (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isCohenMacaulayAt_point» := P2M_GroundTheory_Heights__Heights_isCohenMacaulayAt_point_bc8cbda9b5ee
