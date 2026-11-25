-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_aeval_cons_eq_eval__finSuccEquiv_b773e260af41
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_aeval_cons_eq_eval__finSuccEquiv_b773e260af41
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:39:52.92656+00:00
-- url     : https://prove2.me/theorems/e5d11b29-296c-4e29-bd78-9ab84125849a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets aeval cons eq eval  fin Succ Equiv b773e260af41: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Comp
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets aeval cons eq eval  fin Succ Equiv b773e260af41 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets aeval cons eq eval  fin Succ Equiv b773e260af41 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProjectionCoordinateEquation.lean#L12-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProjectionCoordinateEquation.lean#L12-L27

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProjectionCoordinateEquation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProjectionCoordinateEquation
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
open MvPolynomial Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_aeval_cons_eq_eval__finSuccEquiv_b773e260af41 {k : ℕ} {B : Type*} [CommRing B] [Algebra ℂ B] (b : B)
    (y : Fin k → B) (P : MvPolynomial (Fin (k + 1)) ℂ) :
    aeval (Fin.cons b y : Fin (k + 1) → B) P =
      Polynomial.eval₂ (aeval y).toRingHom b (finSuccEquiv ℂ k P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«aeval_cons_eq_eval₂_finSuccEquiv» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_aeval_cons_eq_eval__finSuccEquiv_b773e260af41
