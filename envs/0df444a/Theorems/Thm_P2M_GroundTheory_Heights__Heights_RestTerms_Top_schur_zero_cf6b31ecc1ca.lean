-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_schur_zero_cf6b31ecc1ca
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_schur_zero_cf6b31ecc1ca
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:50.953939+00:00
-- url     : https://prove2.me/theorems/1d47016e-d068-413d-9316-e053cc765d02
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top schur zero cf6b31ecc1ca: P2 M Ground Theory Heights  Heights Rest Terms Top schur zero cf6b31ecc1ca
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top schur zero cf6b31ecc1ca construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top schur zero cf6b31ecc1ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L167-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L167-L177

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_schur_zero_cf6b31ecc1ca (σ : Type*) [Fintype σ] [DecidableEq σ] (m : ℕ) :
    schur σ (0 : Fin m → ℕ) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«schur_zero» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_schur_zero_cf6b31ecc1ca
