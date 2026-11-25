-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockPermute_blockEmb_50bfbd9b99dc
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockPermute_blockEmb_50bfbd9b99dc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:21:13.330894+00:00
-- url     : https://prove2.me/theorems/4b2c4908-da37-4a16-81d0-e1c402b47381
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top block Permute block Emb 50bfbd9b99dc: P2 M Ground Theory Heights  Heights Rest Terms Top block Permute block Emb 50bfbd9b99dc
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top block Permute block Emb 50bfbd9b99dc construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top block Permute block Emb 50bfbd9b99dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L18-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
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
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockPermute_blockEmb_50bfbd9b99dc (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) (σ : Fin f)
    (P : RootRing 1 N) :
    blockPermute f N w (blockEmb f N σ P) =
      blockEmb f N σ (blockPermute 1 N (fun _ => w σ) P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«blockPermute_blockEmb» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockPermute_blockEmb_50bfbd9b99dc
