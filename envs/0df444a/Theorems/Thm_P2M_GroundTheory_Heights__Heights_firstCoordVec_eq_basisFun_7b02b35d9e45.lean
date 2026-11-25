-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_firstCoordVec_eq_basisFun_7b02b35d9e45
-- name    : P2M_GroundTheory_Heights__Heights_firstCoordVec_eq_basisFun_7b02b35d9e45
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:46:33.488771+00:00
-- url     : https://prove2.me/theorems/c0f816e7-7c62-4150-9472-097b329ccca2
-- title:
--   P2 M Ground Theory Heights  Heights first Coord Vec eq basis Fun 7b02b35d9e45: P2 M Ground Theory Heights  Heights first Coord Vec eq basis Fun 7b02b35d9e45
-- statement:
--   The P2 M Ground Theory Heights  Heights first Coord Vec eq basis Fun 7b02b35d9e45 construction uses the P2 M Ground Theory Heights  Heights first Coord Vec eq basis Fun 7b02b35d9e45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussInvariant.lean#L106-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussInvariant.lean#L106-L109

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentGaussInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentGaussInvariant
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
open MeasureTheory Module
open scoped Matrix
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_firstCoordVec_eq_basisFun_7b02b35d9e45 {n : ℕ} (hn : 0 < n) :
    firstCoordVec n = EuclideanSpace.basisFun (Fin n) ℂ ⟨0, hn⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«firstCoordVec_eq_basisFun» := P2M_GroundTheory_Heights__Heights_firstCoordVec_eq_basisFun_7b02b35d9e45
