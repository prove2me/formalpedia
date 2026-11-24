-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_card_blockPerm_c7329941447d
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_card_blockPerm_c7329941447d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:42.834505+00:00
-- url     : https://prove2.me/theorems/4c40d79d-ece6-4680-b762-ddbd5d123e6a
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag card block Perm c7329941447d: P2 M Ground Theory Heights  Heights Rest Terms Flag card block Perm c7329941447d
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag card block Perm c7329941447d construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag card block Perm c7329941447d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L102-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L102-L103

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_card_blockPerm_c7329941447d (f N : ℕ) : Fintype.card (Fin f → Equiv.Perm (Fin N)) = N.factorial ^ f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«card_blockPerm» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_card_blockPerm_c7329941447d
