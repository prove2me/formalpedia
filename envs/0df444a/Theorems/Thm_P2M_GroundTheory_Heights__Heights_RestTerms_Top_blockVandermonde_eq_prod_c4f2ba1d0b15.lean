-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockVandermonde_eq_prod_c4f2ba1d0b15
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockVandermonde_eq_prod_c4f2ba1d0b15
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:21:12.987873+00:00
-- url     : https://prove2.me/theorems/f5dc0215-ad8a-49e1-b103-aea7013e6401
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top block Vandermonde eq prod c4f2ba1d0b15: P2 M Ground Theory Heights  Heights Rest Terms Top block Vandermonde eq prod c4f2ba1d0b15
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top block Vandermonde eq prod c4f2ba1d0b15 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top block Vandermonde eq prod c4f2ba1d0b15 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L92-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L92-L95

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockVandermonde_eq_prod_c4f2ba1d0b15 (f N : ℕ) :
    blockVandermonde f N = ∏ σ : Fin f, blockEmb f N σ (blockVandermonde 1 N) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«blockVandermonde_eq_prod» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockVandermonde_eq_prod_c4f2ba1d0b15
