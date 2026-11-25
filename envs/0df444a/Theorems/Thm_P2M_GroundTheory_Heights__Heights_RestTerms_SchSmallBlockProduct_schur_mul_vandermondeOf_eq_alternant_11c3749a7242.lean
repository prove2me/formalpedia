-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchSmallBlockProduct_schur_mul_vandermondeOf_eq_alternant_11c3749a7242
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_SchSmallBlockProduct_schur_mul_vandermondeOf_eq_alternant_11c3749a7242
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:20:51.498301+00:00
-- url     : https://prove2.me/theorems/6556fd12-3a5b-5e45-9e23-eb859d18ad67
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Sch Small Block Product schur mul vandermonde Of eq alternant 11c3749a7242: P2 M Ground Theory Heights  Heights Rest Terms Sch Small Block Product schur
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Sch Small Block Product schur mul vandermonde Of eq alternant 11c3749a7242 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Sch Small Block Product schur mul vandermonde Of eq alternant 11c3749a7242 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchSmallBlockProduct.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchSmallBlockProduct.lean#L29-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchSmallBlockProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_SchSmallBlockProduct_schur_mul_vandermondeOf_eq_alternant_11c3749a7242 {m : ℕ} (lam : Fin m → ℕ) :
    schur (Fin m) lam * vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) =
      alternant (fun i : Fin m => lam i + (m - 1 - (i : ℕ))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«SchSmallBlockProduct».«schur_mul_vandermondeOf_eq_alternant» := P2M_GroundTheory_Heights__Heights_RestTerms_SchSmallBlockProduct_schur_mul_vandermondeOf_eq_alternant_11c3749a7242
