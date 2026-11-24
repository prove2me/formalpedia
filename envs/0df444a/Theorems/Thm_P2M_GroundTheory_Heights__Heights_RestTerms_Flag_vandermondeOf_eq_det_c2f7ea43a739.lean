-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_vandermondeOf_eq_det_c2f7ea43a739
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_vandermondeOf_eq_det_c2f7ea43a739
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:11:03.803796+00:00
-- url     : https://prove2.me/theorems/babb12e6-b22a-4340-b44f-ad0b55dd4890
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag vandermonde Of eq det c2f7ea43a739: P2 M Ground Theory Heights  Heights Rest Terms Flag vandermonde Of eq det c2f7ea43a739
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag vandermonde Of eq det c2f7ea43a739 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag vandermonde Of eq det c2f7ea43a739 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L15-L19

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_vandermondeOf_eq_det_c2f7ea43a739 {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R) :
    vandermondeOf v = (Matrix.vandermonde (fun i => -v i)).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«vandermondeOf_eq_det» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_vandermondeOf_eq_det_c2f7ea43a739
