-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_antisymmetrize_63f7c060ed6c
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_antisymmetrize_63f7c060ed6c
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:43.757933+00:00
-- url     : https://prove2.me/theorems/1891d38b-da23-5de8-b627-8fbd8ea5b728
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag block Permute antisymmetrize 63f7c060ed6c: P2 M Ground Theory Heights  Heights Rest Terms Flag block Permute antisymmetrize 63f7c060ed6c
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag block Permute antisymmetrize 63f7c060ed6c construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag block Permute antisymmetrize 63f7c060ed6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L94-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L94-L100

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_antisymmetrize_63f7c060ed6c (f N : ℕ) (v : Fin f → Equiv.Perm (Fin N)) (H : RootRing f N) :
    blockPermute f N v (antisymmetrize f N H) = blockSign f N v • antisymmetrize f N H := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«blockPermute_antisymmetrize» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_antisymmetrize_63f7c060ed6c
