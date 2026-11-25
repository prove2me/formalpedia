-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_prod_39abdaefbbe5
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_prod_39abdaefbbe5
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:20:50.088859+00:00
-- url     : https://prove2.me/theorems/88f3d8f8-f0ec-40a9-874d-ee06429d1fea
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top antisymmetrize prod 39abdaefbbe5: P2 M Ground Theory Heights  Heights Rest Terms Top antisymmetrize prod 39abdaefbbe5
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top antisymmetrize prod 39abdaefbbe5 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top antisymmetrize prod 39abdaefbbe5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L106-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L106-L112

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_prod_39abdaefbbe5 (f N : ℕ) (P : Fin f → RootRing 1 N) :
    antisymmetrize f N (∏ σ, blockEmb f N σ (P σ)) =
      ∏ σ, blockEmb f N σ (antisymmetrize 1 N (P σ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«antisymmetrize_prod» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_prod_39abdaefbbe5
