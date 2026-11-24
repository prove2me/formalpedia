-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_pow_mul_mem_of_aeval_chartSubst_mem_9a4afa4e37e2
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_pow_mul_mem_of_aeval_chartSubst_mem_9a4afa4e37e2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:41.042031+00:00
-- url     : https://prove2.me/theorems/e7b60cfa-50da-4f75-9663-848ee87a4f26
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR exists pow mul mem of aeval chart Subst mem 9a4afa4e37e2: P2 M Ground Theory Heights  Heights Numbers DVR exists pow mul mem of aeval chart Subst mem 9a
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR exists pow mul mem of aeval chart Subst mem 9a4afa4e37e2 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR exists pow mul mem of aeval chart Subst mem 9a4afa4e37e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpHorizontalSat.lean#L18-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpHorizontalSat.lean#L18-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AevalChartSubstMemOfMemBlowUpOf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalSat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
noncomputable section
variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_pow_mul_mem_of_aeval_chartSubst_mem_9a4afa4e37e2 {P : Ideal (MRing ι R)} {u a : J → MRing ι R}
    {W : Ideal (MRing ι R)} (j₀ : J)
    (hrel : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ blowUpOf P u)
    {F : MRing (extIdx ι J) R}
    (hF : aeval (chartSubst a) F ∈ Ideal.map (Polynomial.C : MRing ι R →+* Polynomial (MRing ι R)) W) :
    ∃ n : ℕ, liftForm (a j₀ ^ n) * F ∈
      blowUpOf P u ⊔ Ideal.map (liftForm (J := J) : MRing ι R →ₐ[R] MRing (extIdx ι J) R) W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«exists_pow_mul_mem_of_aeval_chartSubst_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_pow_mul_mem_of_aeval_chartSubst_mem_9a4afa4e37e2
