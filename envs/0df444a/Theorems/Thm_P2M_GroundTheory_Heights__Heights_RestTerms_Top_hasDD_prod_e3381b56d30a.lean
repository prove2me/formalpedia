-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_prod_e3381b56d30a
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_prod_e3381b56d30a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:21:35.621356+00:00
-- url     : https://prove2.me/theorems/ec8adc88-416f-597d-8a5f-501a29af20f7
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top has DD prod e3381b56d30a: P2 M Ground Theory Heights  Heights Rest Terms Top has DD prod e3381b56d30a
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top has DD prod e3381b56d30a construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top has DD prod e3381b56d30a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L114-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L114-L118

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_prod_e3381b56d30a (f N : ℕ) (P Q : Fin f → RootRing 1 N) (h : ∀ σ, HasDD 1 N (P σ) (Q σ)) :
    HasDD f N (∏ σ, blockEmb f N σ (P σ)) (∏ σ, blockEmb f N σ (Q σ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«hasDD_prod» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_prod_e3381b56d30a
