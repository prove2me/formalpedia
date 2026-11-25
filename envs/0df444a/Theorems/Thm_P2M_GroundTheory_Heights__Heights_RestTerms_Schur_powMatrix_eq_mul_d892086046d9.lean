-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_powMatrix_eq_mul_d892086046d9
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Schur_powMatrix_eq_mul_d892086046d9
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:20:56.663021+00:00
-- url     : https://prove2.me/theorems/841ba3af-dbf7-4723-9af0-7be89b4373c4
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Schur pow Matrix eq mul d892086046d9: P2 M Ground Theory Heights  Heights Rest Terms Schur pow Matrix eq mul d892086046d9
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Schur pow Matrix eq mul d892086046d9 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Schur pow Matrix eq mul d892086046d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L172-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L172-L186

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
variable {m : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Schur_powMatrix_eq_mul_d892086046d9 (α : Fin m → ℕ) :
    (Matrix.of fun i j : Fin m => (X j : MvPolynomial (Fin m) ℚ) ^ α i) =
      hMatrix α * omitProductCoeffMatrix m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Schur».«powMatrix_eq_mul» := P2M_GroundTheory_Heights__Heights_RestTerms_Schur_powMatrix_eq_mul_d892086046d9
