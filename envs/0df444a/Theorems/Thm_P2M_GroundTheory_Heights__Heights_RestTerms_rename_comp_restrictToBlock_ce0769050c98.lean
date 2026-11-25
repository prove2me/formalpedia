-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rename_comp_restrictToBlock_ce0769050c98
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_rename_comp_restrictToBlock_ce0769050c98
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:35:53.878804+00:00
-- url     : https://prove2.me/theorems/6736d417-a698-5c07-bd62-71fabd28d223
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms rename comp restrict To Block ce0769050c98: P2 M Ground Theory Heights  Heights Rest Terms rename comp restrict To Block ce0769050c98
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms rename comp restrict To Block ce0769050c98 construction uses the P2 M Ground Theory Heights  Heights Rest Terms rename comp restrict To Block ce0769050c98 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagRestrictSymmetric.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagRestrictSymmetric.lean#L11-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagRestrictSymmetric
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
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_RestTerms_rename_comp_restrictToBlock_ce0769050c98 (f N : ℕ) (τ : Fin f) (π : Equiv.Perm (Fin N)) :
    (rename π).comp (restrictToBlock f N τ) =
      (restrictToBlock f N τ).comp (blockPermute f N (Function.update 1 τ π)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«rename_comp_restrictToBlock» := P2M_GroundTheory_Heights__Heights_RestTerms_rename_comp_restrictToBlock_ce0769050c98
