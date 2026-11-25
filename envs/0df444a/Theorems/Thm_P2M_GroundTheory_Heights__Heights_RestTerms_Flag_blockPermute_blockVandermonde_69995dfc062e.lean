-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_blockVandermonde_69995dfc062e
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_blockVandermonde_69995dfc062e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:27.07629+00:00
-- url     : https://prove2.me/theorems/32048c4d-efc9-4531-b924-d4f7136691b8
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag block Permute block Vandermonde 69995dfc062e: P2 M Ground Theory Heights  Heights Rest Terms Flag block Permute block Vandermonde 69995dfc062e
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag block Permute block Vandermonde 69995dfc062e construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag block Permute block Vandermonde 69995dfc062e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L67-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L67-L81

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_blockVandermonde_69995dfc062e (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) :
    blockPermute f N w (blockVandermonde f N) = blockSign f N w • blockVandermonde f N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«blockPermute_blockVandermonde» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_blockVandermonde_69995dfc062e
