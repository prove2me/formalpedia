-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_schur_isSymmetric_e777444d0d85
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Schur_schur_isSymmetric_e777444d0d85
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:31:34.905792+00:00
-- url     : https://prove2.me/theorems/b002f9b4-9151-4c89-982b-5c760030be91
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Schur schur is Symmetric e777444d0d85: P2 M Ground Theory Heights  Heights Rest Terms Schur schur is Symmetric e777444d0d85
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Schur schur is Symmetric e777444d0d85 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Schur schur is Symmetric e777444d0d85 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L311-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L311-L318

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Schur
open MvPolynomial Finset
noncomputable section
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Schur_schur_isSymmetric_e777444d0d85 {r : ℕ} (lam : Fin r → ℕ) : (schur σ lam).IsSymmetric := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Schur».«schur_isSymmetric» := P2M_GroundTheory_Heights__Heights_RestTerms_Schur_schur_isSymmetric_e777444d0d85
