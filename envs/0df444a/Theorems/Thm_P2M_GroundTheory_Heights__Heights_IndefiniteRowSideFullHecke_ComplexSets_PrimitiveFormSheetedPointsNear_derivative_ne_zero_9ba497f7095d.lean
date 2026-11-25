-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormSheetedPointsNear_derivative_ne_zero_9ba497f7095d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormSheetedPointsNear_derivative_ne_zero_9ba497f7095d
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:17.762167+00:00
-- url     : https://prove2.me/theorems/8b771e19-c927-57b9-85a8-982a91636c95
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Primitive Form Sheeted Points Near derivative ne zero 9ba497f7095d: P2 M Ground Theory Heights  Heights Indefinite Row S
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Primitive Form Sheeted Points Near derivative ne zero 9ba497f7095d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Primitive Form Sheeted Points Near derivative ne zero 9ba497f7095d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitiveFormSheetedPointsNear.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitiveFormSheetedPointsNear.lean#L24-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedPointsNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormMinimalFactorPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticSimpleRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveFormSheetedPointsNear
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
open Topology Filter

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormSheetedPointsNear_derivative_ne_zero_9ba497f7095d (n : ℕ) (c : Fin n → ℂ) (τ : ℂ)
    (hs : (Polynomial.X ^ n + ∑ j, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable)
    (hτ : τ ^ n + ∑ j, c j * τ ^ (j : ℕ) = 0) :
    (Polynomial.X ^ n + ∑ j, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).derivative.eval τ ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«PrimitiveFormSheetedPointsNear».«derivative_ne_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormSheetedPointsNear_derivative_ne_zero_9ba497f7095d
