-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_SectionNef_hyps_15e71ba9a296
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_SectionNef_hyps_15e71ba9a296
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:24:41.183395+00:00
-- url     : https://prove2.me/theorems/977832ee-8bbf-4e5f-8315-5682f888eaf9
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Section Nef hyps 15e71ba9a296: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Section Nef hyps 15e71b
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Section Nef hyps 15e71ba9a296 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Section Nef hyps 15e71ba9a296 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsIsoPullbackObjUnitToUnit.lean#L478-L501
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsIsoPullbackObjUnitToUnit.lean#L478-L501

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_WeilDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory Opposite AlgebraicGeometry Limits TopologicalSpace MonoidalCategory
open GroundTheory.Arith.SchemeCoh
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_SectionNef_hyps_15e71ba9a296 :
    IsMultiProjPrime (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) ∧
    ringKrullDim (MRing (fun _ : Unit => Fin 2) ℚ ⧸ (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ))) =
      ((1 + Fintype.card Unit : ℕ) : WithBot ℕ∞) ∧
    ((∃ s : MRing (fun _ : Unit => Fin 2) ℚ, IsMultiHomog s (fun _ => 1) ∧ s ∉ (⊥ : Ideal _)) ∨
      (∀ W : Ideal (MRing (fun _ : Unit => Fin 2) ℚ), IsMultiProjPrime W → ⊥ ≤ W →
        ∃ s : MRing (fun _ : Unit => Fin 2) ℚ, IsMultiHomog s (fun _ => 1) ∧ s ∉ W)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«SectionNef».«hyps» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_SectionNef_hyps_15e71ba9a296
