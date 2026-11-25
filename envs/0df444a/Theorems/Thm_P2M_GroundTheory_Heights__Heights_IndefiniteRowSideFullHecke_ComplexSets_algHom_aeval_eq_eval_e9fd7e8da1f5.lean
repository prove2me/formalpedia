-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_algHom_aeval_eq_eval_e9fd7e8da1f5
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_algHom_aeval_eq_eval_e9fd7e8da1f5
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:39:29.992396+00:00
-- url     : https://prove2.me/theorems/5feb236c-ed03-5aa0-86ef-41e6fefbdd59
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets alg Hom aeval eq eval e9fd7e8da1f5: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets alg
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets alg Hom aeval eq eval e9fd7e8da1f5 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets alg Hom aeval eq eval e9fd7e8da1f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProjectionCoordinateEquation.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProjectionCoordinateEquation.lean#L48-L51

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_algHom_aeval_eq_eval_e9fd7e8da1f5 {σ : Type*} {B : Type*} [CommRing B] [Algebra ℂ B] (e : B →ₐ[ℂ] ℂ)
    (v : σ → B) (P : MvPolynomial σ ℂ) : e (aeval v P) = eval (fun i => e (v i)) P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«algHom_aeval_eq_eval» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_algHom_aeval_eq_eval_e9fd7e8da1f5
