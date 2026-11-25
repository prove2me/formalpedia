-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_nonempty_normalModel_of_presentation_27235b04eeff
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_nonempty_normalModel_of_presentation_27235b04eeff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:33:50.778151+00:00
-- url     : https://prove2.me/theorems/7d613221-0f57-5c58-ad6e-a36f7404162c
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets nonempty normal Model of presentation 27235b04eeff: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke C
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets nonempty normal Model of presentation 27235b04eeff construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets nonempty normal Model of presentation 27235b04eeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalModelExists.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalModelExists.lean#L36-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelExists
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NonemptyNormalModelOfPresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelExists
import Theorems.Thm_UpperTheory_Reformulated_B_Gc5_nonempty_normalModel_of_presentation

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
open MvPolynomial
noncomputable section
attribute [local instance] FractionRing.liftAlgebra

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_nonempty_normalModel_of_presentation_27235b04eeff {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (R : Type)
    [CommRing R] [IsDomain R] [Algebra ℂ R] (π : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R)
    (hπ : Function.Surjective π) (hker : RingHom.ker π = J) : Nonempty (NormalModel J) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«nonempty_normalModel_of_presentation» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_nonempty_normalModel_of_presentation_27235b04eeff
