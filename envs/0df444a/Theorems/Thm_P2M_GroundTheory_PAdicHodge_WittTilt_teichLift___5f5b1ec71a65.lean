-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_WittTilt_teichLift___5f5b1ec71a65
-- name    : P2M_GroundTheory_PAdicHodge_WittTilt_teichLift___5f5b1ec71a65
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:38:04.62147+00:00
-- url     : https://prove2.me/theorems/b48906a2-cf0f-4718-be10-51112f637601
-- title:
--   P2 M Ground Theory PAdic Hodge Witt Tilt teich Lift   5f5b1ec71a65: P2 M Ground Theory PAdic Hodge Witt Tilt teich Lift   5f5b1ec71a65
-- statement:
--   The P2 M Ground Theory PAdic Hodge Witt Tilt teich Lift   5f5b1ec71a65 construction uses the P2 M Ground Theory PAdic Hodge Witt Tilt teich Lift   5f5b1ec71a65 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonLift.lean#L98-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonLift.lean#L98-L98

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.WittTilt
open _root_.WittVector
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "𝔸" => Localization.Away (p : AInf K p)

theorem P2M_GroundTheory_PAdicHodge_WittTilt_teichLift___5f5b1ec71a65 : (teichLift K p).π = (p : WittVector p K♭) := by sorry

alias «GroundTheory».«PAdicHodge».«WittTilt».«teichLift_π» := P2M_GroundTheory_PAdicHodge_WittTilt_teichLift___5f5b1ec71a65

attribute [defeq] P2M_GroundTheory_PAdicHodge_WittTilt_teichLift___5f5b1ec71a65
