-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_vandermondeOf_perm_3aea40e9f6fb
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_vandermondeOf_perm_3aea40e9f6fb
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:56.449813+00:00
-- url     : https://prove2.me/theorems/9be78161-cc4f-43d6-b348-4a7f10485ba8
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag vandermonde Of perm 3aea40e9f6fb: P2 M Ground Theory Heights  Heights Rest Terms Flag vandermonde Of perm 3aea40e9f6fb
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag vandermonde Of perm 3aea40e9f6fb construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag vandermonde Of perm 3aea40e9f6fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L21-L28

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_vandermondeOf_perm_3aea40e9f6fb {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R)
    (σ : Equiv.Perm (Fin m)) :
    vandermondeOf (fun i => v (σ i)) = (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * vandermondeOf v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«vandermondeOf_perm» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_vandermondeOf_perm_3aea40e9f6fb
