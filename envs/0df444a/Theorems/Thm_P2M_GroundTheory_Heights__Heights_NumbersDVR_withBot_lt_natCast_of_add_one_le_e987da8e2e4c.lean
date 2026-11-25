-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_lt_natCast_of_add_one_le_e987da8e2e4c
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_lt_natCast_of_add_one_le_e987da8e2e4c
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:12:52.373693+00:00
-- url     : https://prove2.me/theorems/69a085d5-55c5-4746-af20-edeb8f48b07e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR with Bot lt nat Cast of add one le e987da8e2e4c: P2 M Ground Theory Heights  Heights Numbers DVR with Bot lt nat Cast of add one le e987da8e2e4c
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR with Bot lt nat Cast of add one le e987da8e2e4c construction uses the P2 M Ground Theory Heights  Heights Numbers DVR with Bot lt nat Cast of add one le e987da8e2e4c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WithBotLtNatCastOfAddOneLe.lean#L30-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WithBotLtNatCastOfAddOneLe.lean#L30-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivisorIdealBotUniformiser
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleFiniteSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_WithBotLtNatCastOfAddOneLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
variable {A : Type*} [CommRing A]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_lt_natCast_of_add_one_le_e987da8e2e4c (x : WithBot ℕ∞) (N : ℕ) (h : x + 1 ≤ (N : WithBot ℕ∞)) :
    x < (N : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«withBot_lt_natCast_of_add_one_le» := P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_lt_natCast_of_add_one_le_e987da8e2e4c
