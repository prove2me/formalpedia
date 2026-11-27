-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_TwoExpansionsAgree_hyp_inhabited_146b61f05b4c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_TwoExpansionsAgree_hyp_inhabited_146b61f05b4c
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:25:45.22804+00:00
-- url     : https://prove2.me/theorems/fcc836f0-a4af-5de4-bbf1-63730db6b471
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR Two Expansions Agree hyp inhabited 146b61f05b4c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbe
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR Two Expansions Agree hyp inhabited 146b61f05b4c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR Two Expansions Agree hyp inhabited 146b61f05b4c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/TrivBundleIsTwistedForms.lean#L341-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/TrivBundleIsTwistedForms.lean#L341-L355

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_TwoExpansionsAgree_hyp_inhabited_146b61f05b4c :
    Irreducible ((2 : ℕ) : ℤ_[2]) ∧
      IsModelOver (⊥ : Ideal (MRingOver ℤ_[2] (fun _ : Unit => Fin 2))) 1 ∧
      RingHom.ker (genPt ℤ_[2] (fun _ : Unit => Fin 2)) = ⊥ ∧
      SameGenericFibre ((2 : ℕ) : ℤ_[2])
        (trivBundle ℤ_[2] (segreVec (genPt ℤ_[2] (fun _ : Unit => Fin 2))) 2)
        (trivBundle ℤ_[2] (segreVec (genPt ℤ_[2] (fun _ : Unit => Fin 2))) 2) ∧
      IsFlagPair (genPt ℤ_[2] (fun _ : Unit => Fin 2)) ⊥
        (trivBundle ℤ_[2] (segreVec (genPt ℤ_[2] (fun _ : Unit => Fin 2))) 2)
        (trivBundle ℤ_[2] (segreVec (genPt ℤ_[2] (fun _ : Unit => Fin 2))) 2)
        (Pi.basisFun _ (Fin 2)) 0 0 1 1 1 1 ∧
      (esymm (Fin 2) ℤ 2).IsSymmetric ∧ (esymm (Fin 2) ℤ 2).IsHomogeneous (1 + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«NumbersDVR».«TwoExpansionsAgree».«hyp_inhabited» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_TwoExpansionsAgree_hyp_inhabited_146b61f05b4c
