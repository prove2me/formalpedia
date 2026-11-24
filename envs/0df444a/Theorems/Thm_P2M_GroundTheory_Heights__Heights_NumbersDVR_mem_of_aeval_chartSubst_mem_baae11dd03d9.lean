-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_of_aeval_chartSubst_mem_baae11dd03d9
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_of_aeval_chartSubst_mem_baae11dd03d9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:31.274718+00:00
-- url     : https://prove2.me/theorems/c56d32a8-5448-4b6f-a47c-f29d8ef914fa
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR mem of aeval chart Subst mem baae11dd03d9: P2 M Ground Theory Heights  Heights Numbers DVR mem of aeval chart Subst mem baae11dd03d9
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR mem of aeval chart Subst mem baae11dd03d9 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR mem of aeval chart Subst mem baae11dd03d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/AevalChartSubstMemOfMemBlowUpOf.lean#L64-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/AevalChartSubstMemOfMemBlowUpOf.lean#L64-L105

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AevalChartSubstMemOfMemBlowUpOf
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_of_aeval_chartSubst_mem_baae11dd03d9 {a : J → MRing ι R} {H : Ideal (MRing (extIdx ι J) R)}
    (hH : H.IsPrime) {P' : Ideal (MRing ι R)} (hP'H : P' ≤ H.comap (liftForm (J := J))) (j₀ : J)
    (ha : liftForm (a j₀) ∉ H)
    (hrel : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ H)
    {F : MRing (extIdx ι J) R}
    (hF : aeval (chartSubst a) F ∈ Ideal.map (Polynomial.C : MRing ι R →+* Polynomial (MRing ι R)) P') :
    F ∈ H := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«mem_of_aeval_chartSubst_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_of_aeval_chartSubst_mem_baae11dd03d9
