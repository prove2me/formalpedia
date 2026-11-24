-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_coeff_psiPoly_9cd5be07914d
-- name    : P2M_GroundTheory_Heights__Heights_KRest_coeff_psiPoly_9cd5be07914d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:16.656347+00:00
-- url     : https://prove2.me/theorems/c07a0588-1567-4799-9ac7-1200adbea561
-- title:
--   P2 M Ground Theory Heights  Heights KRest coeff psi Poly 9cd5be07914d: P2 M Ground Theory Heights  Heights KRest coeff psi Poly 9cd5be07914d
-- statement:
--   The P2 M Ground Theory Heights  Heights KRest coeff psi Poly 9cd5be07914d construction uses the P2 M Ground Theory Heights  Heights KRest coeff psi Poly 9cd5be07914d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/RestCutBasic.lean#L99-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/RestCutBasic.lean#L99-L101

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

theorem P2M_GroundTheory_Heights__Heights_KRest_coeff_psiPoly_9cd5be07914d {σ : Type*} (ψ : ℝ →ₗ[ℚ] ℚ) (P : MvPolynomial σ ℝ) (β : σ →₀ ℕ) :
    coeff β (psiPoly ψ P) = ψ (coeff β P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KRest».«coeff_psiPoly» := P2M_GroundTheory_Heights__Heights_KRest_coeff_psiPoly_9cd5be07914d
