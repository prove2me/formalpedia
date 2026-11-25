-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_integralClosure_fractionRing_finite_54f1a691493f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_integralClosure_fractionRing_finite_54f1a691493f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:27:50.057093+00:00
-- url     : https://prove2.me/theorems/010a7cd0-5e76-5f91-8689-bb076674542f
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets integral Closure fraction Ring finite 54f1a691493f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke C
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets integral Closure fraction Ring finite 54f1a691493f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets integral Closure fraction Ring finite 54f1a691493f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalModelExists.lean#L14-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalModelExists.lean#L14-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelExists
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NonemptyNormalModelOfPresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelExists
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_integralClosure_fractionRing_finite_54f1a691493f (R : Type) [CommRing R] [IsDomain R] [Algebra ℂ R]
    [Algebra.FiniteType ℂ R] : Module.Finite R (integralClosure R (FractionRing R)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«integralClosure_fractionRing_finite» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_integralClosure_fractionRing_finite_54f1a691493f
