-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_blockPermute_98b261a82348
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_blockPermute_98b261a82348
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:48.804828+00:00
-- url     : https://prove2.me/theorems/71fc7e11-710d-4bae-a149-e8c6588c61ce
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag block Permute block Permute 98b261a82348: P2 M Ground Theory Heights  Heights Rest Terms Flag block Permute block Permute 98b261a82348
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag block Permute block Permute 98b261a82348 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag block Permute block Permute 98b261a82348 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L47-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_blockPermute_98b261a82348 (f N : ℕ) (v w : Fin f → Equiv.Perm (Fin N)) (H : RootRing f N) :
    blockPermute f N v (blockPermute f N w H) = blockPermute f N (v * w) H := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«blockPermute_blockPermute» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_blockPermute_98b261a82348
