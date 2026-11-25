-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_psiPoly_map_mul_4d01b38de564
-- name    : P2M_GroundTheory_Heights__Heights_KRest_psiPoly_map_mul_4d01b38de564
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:59.008806+00:00
-- url     : https://prove2.me/theorems/afab86f5-761c-436e-bf3b-1afa2fd40db1
-- title:
--   P2 M Ground Theory Heights  Heights KRest psi Poly map mul 4d01b38de564: P2 M Ground Theory Heights  Heights KRest psi Poly map mul 4d01b38de564
-- statement:
--   The P2 M Ground Theory Heights  Heights KRest psi Poly map mul 4d01b38de564 construction uses the P2 M Ground Theory Heights  Heights KRest psi Poly map mul 4d01b38de564 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/RestCutBasic.lean#L103-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/RestCutBasic.lean#L103-L109

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_RestCutBasic
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
open GroundTheory.Heights₂.Heights.KRest
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_KRest_psiPoly_map_mul_4d01b38de564 {σ : Type*} (ψ : ℝ →ₗ[ℚ] ℚ) (A : MvPolynomial σ ℚ)
    (P : MvPolynomial σ ℝ) : psiPoly ψ (map (algebraMap ℚ ℝ) A * P) = A * psiPoly ψ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KRest».«psiPoly_map_mul» := P2M_GroundTheory_Heights__Heights_KRest_psiPoly_map_mul_4d01b38de564
