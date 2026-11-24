-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_X_536c027402b7
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_X_536c027402b7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:50.713192+00:00
-- url     : https://prove2.me/theorems/2c15c33a-404f-4597-9313-59e93ca1cc22
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag block Permute X 536c027402b7: P2 M Ground Theory Heights  Heights Rest Terms Flag block Permute X 536c027402b7
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag block Permute X 536c027402b7 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag block Permute X 536c027402b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L63-L65

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_X_536c027402b7 (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) (τ : Fin f) (i : Fin N) :
    blockPermute f N w (X (τ, i)) = X (τ, w τ i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«blockPermute_X» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_X_536c027402b7
