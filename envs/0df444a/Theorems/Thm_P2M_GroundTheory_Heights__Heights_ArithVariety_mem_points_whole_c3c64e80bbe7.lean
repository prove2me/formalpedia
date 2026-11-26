-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mem_points_whole_c3c64e80bbe7
-- name    : P2M_GroundTheory_Heights__Heights_ArithVariety_mem_points_whole_c3c64e80bbe7
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:07:56.510735+00:00
-- url     : https://prove2.me/theorems/8497159c-f688-4699-bcd2-84adbfccc1d6
-- title:
--   P2 M Ground Theory Heights  Heights Arith Variety mem points whole c3c64e80bbe7: P2 M Ground Theory Heights  Heights Arith Variety mem points whole c3c64e80bbe7
-- statement:
--   The P2 M Ground Theory Heights  Heights Arith Variety mem points whole c3c64e80bbe7 construction uses the P2 M Ground Theory Heights  Heights Arith Variety mem points whole c3c64e80bbe7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Points.lean#L63-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Points.lean#L63-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Points
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
open MvPolynomial NumberField
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.ArithVariety
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_ArithVariety_mem_points_whole_c3c64e80bbe7 {F : Type*} [CommRing F] {z : Cone n F} (hz : BlockNonzero z) :
    z ∈ (whole n).points F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ArithVariety».«mem_points_whole» := P2M_GroundTheory_Heights__Heights_ArithVariety_mem_points_whole_c3c64e80bbe7
