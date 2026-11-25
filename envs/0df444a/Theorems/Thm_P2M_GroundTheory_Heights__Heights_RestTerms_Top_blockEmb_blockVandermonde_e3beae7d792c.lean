-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockEmb_blockVandermonde_e3beae7d792c
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockEmb_blockVandermonde_e3beae7d792c
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:20:36.453844+00:00
-- url     : https://prove2.me/theorems/9a665dba-ba1c-4775-aad7-1529a4c80d24
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top block Emb block Vandermonde e3beae7d792c: P2 M Ground Theory Heights  Heights Rest Terms Top block Emb block Vandermonde e3beae7d792c
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top block Emb block Vandermonde e3beae7d792c construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top block Emb block Vandermonde e3beae7d792c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L87-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L87-L90

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockEmb_blockVandermonde_e3beae7d792c (f N : ℕ) (σ : Fin f) :
    blockEmb f N σ (blockVandermonde 1 N) =
      vandermondeOf (fun i : Fin N => (X (σ, i) : RootRing f N)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«blockEmb_blockVandermonde» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockEmb_blockVandermonde_e3beae7d792c
