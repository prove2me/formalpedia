-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_open_image_off_discriminant_0e35fea895a1
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_open_image_off_discriminant_0e35fea895a1
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:41:07.114133+00:00
-- url     : https://prove2.me/theorems/b49adb9d-c36b-4a51-80f9-cbbaa1e9c6d5
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets open image off discriminant 0e35fea895a1: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Set
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets open image off discriminant 0e35fea895a1 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets open image off discriminant 0e35fea895a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalModelOpenMapping.lean#L96-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalModelOpenMapping.lean#L96-L130

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelOpenMapping
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalLocallyIrreducible
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchOffHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericProjectionFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionsContainOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLinearFormCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PUnitaryZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDiscriminantCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelOpenMapping
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_open_image_off_discriminant_0e35fea895a1 (hinj : InjectiveHolomorphicOpen.Statement) {N k : ℕ}
    {I : Ideal (MvPolynomial (Fin N) ℂ)} {A : Matrix (Fin k) (Fin N) ℂ} {P : MvPolynomial (Fin k) ℂ}
    (hP : ∀ y : Fin k → ℂ, eval y P ≠ 0 → ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.fibre I A y,
      ∃ (U : Set (Fin k → ℂ)) (V : Set (Fin N → ℂ)) (g : (Fin k → ℂ) → (Fin N → ℂ)),
        IsOpen U ∧ y ∈ U ∧ IsOpen V ∧ x ∈ V ∧ DifferentiableOn ℂ g U ∧ g y = x ∧
          (∀ w ∈ U, A.mulVec (g w) = w) ∧ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet I ∩ V = g '' U)
    {V : Set (Fin k → ℂ)} {φ : (Fin k → ℂ) → Fin N → ℂ} (hV : IsOpen V) (hφ : DifferentiableOn ℂ φ V)
    (hφi : Set.InjOn φ V) (hφZ : Set.MapsTo φ V (zeroSetIn I)) {t : Fin k → ℂ} (ht : t ∈ V)
    (hPt : eval (A *ᵥ φ t) P ≠ 0) :
    ∃ O : Set (Fin N → ℂ), IsOpen O ∧ φ t ∈ O ∧ zeroSetIn I ∩ O ⊆ φ '' V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«open_image_off_discriminant» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_open_image_off_discriminant_0e35fea895a1
