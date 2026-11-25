-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_cauchyBinet_b49b24ee53ec
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Elem_cauchyBinet_b49b24ee53ec
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:18:59.635966+00:00
-- url     : https://prove2.me/theorems/117d05a3-b964-49e4-9c8c-b2c6d4adbd33
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Elem cauchy Binet b49b24ee53ec: P2 M Ground Theory Heights  Heights Rest Terms Elem cauchy Binet b49b24ee53ec
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Elem cauchy Binet b49b24ee53ec construction uses the P2 M Ground Theory Heights  Heights Rest Terms Elem cauchy Binet b49b24ee53ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Pluecker.lean#L51-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Pluecker.lean#L51-L115

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Pluecker
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
open Matrix Finset
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.Elem
variable {R : Type*} [CommRing R] {κ : Type*}

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Elem_cauchyBinet_b49b24ee53ec [Fintype κ] [DecidableEq κ] {p : ℕ} (A : Matrix (Fin p) κ R) (B : Matrix κ (Fin p) R) :
    (A * B).det = ∑ S : {s : Finset κ // s.card = p},
      (A.submatrix id (subsetCols S)).det * (B.submatrix (subsetCols S) id).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Elem».«cauchyBinet» := P2M_GroundTheory_Heights__Heights_RestTerms_Elem_cauchyBinet_b49b24ee53ec
