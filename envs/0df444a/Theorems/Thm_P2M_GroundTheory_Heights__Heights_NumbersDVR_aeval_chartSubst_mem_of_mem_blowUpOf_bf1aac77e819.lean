-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_chartSubst_mem_of_mem_blowUpOf_bf1aac77e819
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_chartSubst_mem_of_mem_blowUpOf_bf1aac77e819
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:38:34.820111+00:00
-- url     : https://prove2.me/theorems/5342bb86-15f5-43a9-9f04-fb76858cd8fc
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR aeval chart Subst mem of mem blow Up Of bf1aac77e819: P2 M Ground Theory Heights  Heights Numbers DVR aeval chart Subst mem of mem blow Up Of bf1aac77e8
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR aeval chart Subst mem of mem blow Up Of bf1aac77e819 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR aeval chart Subst mem of mem blow Up Of bf1aac77e819 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/AevalChartSubstMemOfMemBlowUpOf.lean#L31-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/AevalChartSubstMemOfMemBlowUpOf.lean#L31-L62

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_chartSubst_mem_of_mem_blowUpOf_bf1aac77e819 {P : Ideal (MRing ι R)} (hP : P.IsPrime)
    {u a : J → MRing ι R} {u₀ g : MRing ι R} (hg : g ∉ P) (h : ∀ j, u₀ * u j - g * a j ∈ P)
    {F : MRing (extIdx ι J) R} (hF : F ∈ blowUpOf P u) :
    aeval (chartSubst a) F ∈ Ideal.map (Polynomial.C : MRing ι R →+* Polynomial (MRing ι R)) P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«aeval_chartSubst_mem_of_mem_blowUpOf» := P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_chartSubst_mem_of_mem_blowUpOf_bf1aac77e819
