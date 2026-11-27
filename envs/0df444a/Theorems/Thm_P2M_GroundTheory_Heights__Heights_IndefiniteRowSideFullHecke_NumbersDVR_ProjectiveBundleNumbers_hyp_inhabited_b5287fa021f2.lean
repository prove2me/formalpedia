-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_ProjectiveBundleNumbers_hyp_inhabited_b5287fa021f2
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_ProjectiveBundleNumbers_hyp_inhabited_b5287fa021f2
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:25:39.512455+00:00
-- url     : https://prove2.me/theorems/09c496ff-c515-5e3d-b83e-e611b5abc58d
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR Projective Bundle Numbers hyp inhabited b5287fa021f2: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR Projective Bundle Numbers hyp inhabited b5287fa021f2 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR Projective Bundle Numbers hyp inhabited b5287fa021f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/TrivBundleIsTwistedForms.lean#L306-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/TrivBundleIsTwistedForms.lean#L306-L315

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
open MvPolynomial Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
universe u v w u₁ u₂
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (o : Type*) [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]
variable {o}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_ProjectiveBundleNumbers_hyp_inhabited_b5287fa021f2 (F : Type*) [Field F] :
    IsProjVarF (⊥ : Ideal (MRingOver F (fun _ : Unit => Fin 2))) 1 ∧
      RingHom.ker (genPt F (fun _ : Unit => Fin 2)) = ⊥ ∧ 1 ≤ 2 ∧
      IsFlagGrading (genPt F (fun _ : Unit => Fin 2))
        (trivBundle F (segreVec (genPt F (fun _ : Unit => Fin 2))) 2) (Pi.basisFun _ (Fin 2)) 0 1 ∧
      IsTwistedForms (genPt F (fun _ : Unit => Fin 2))
        (trivBundle F (segreVec (genPt F (fun _ : Unit => Fin 2))) 2)
        (fun t : Fin 2 => (LinearMap.proj t : (Fin 2 → _) →ₗ[_] _)) 0 ∧ 1 ≤ 2 - 1 + 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«NumbersDVR».«ProjectiveBundleNumbers».«hyp_inhabited» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_ProjectiveBundleNumbers_hyp_inhabited_b5287fa021f2
