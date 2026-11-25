-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_ACris_eval__iota_3d791609d947
-- name    : P2M_GroundTheory_PAdicHodge_ACris_eval__iota_3d791609d947
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:35:39.565926+00:00
-- url     : https://prove2.me/theorems/4dcd2b5d-22c7-5c95-b9b8-08e288eef556
-- title:
--   P2 M Ground Theory PAdic Hodge ACris eval  iota 3d791609d947: P2 M Ground Theory PAdic Hodge ACris eval  iota 3d791609d947
-- statement:
--   The P2 M Ground Theory PAdic Hodge ACris eval  iota 3d791609d947 construction uses the P2 M Ground Theory PAdic Hodge ACris eval  iota 3d791609d947 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisBdR.lean#L390-L392
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisBdR.lean#L390-L392

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_BdRLattice
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_PrecompleteOfSurjective
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open _root_.WittVector
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)

theorem P2M_GroundTheory_PAdicHodge_ACris_eval__iota_3d791609d947 (m : ℕ) (y : ACris K p) :
    _root_.AdicCompletion.evalₐ (kerAway K p) m (iota K p y) = iotaQ K p m y := by sorry

alias «GroundTheory».«PAdicHodge».«ACris».«evalₐ_iota» := P2M_GroundTheory_PAdicHodge_ACris_eval__iota_3d791609d947
