-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolyGermPointPow_coeff_eq_zero_of_isBigO_a896a5b521ef
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolyGermPointPow_coeff_eq_zero_of_isBigO_a896a5b521ef
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:20:10.745632+00:00
-- url     : https://prove2.me/theorems/fcc488d2-fe80-49fe-9404-56b8931dd92b
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Poly Germ Point Pow coeff eq zero of is Big O a896a5b521ef: P2 M Ground Theory Heights  Heights Indefinite Row Side Full
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Poly Germ Point Pow coeff eq zero of is Big O a896a5b521ef construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Poly Germ Point Pow coeff eq zero of is Big O a896a5b521ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPolyGermPointPow.lean#L16-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPolyGermPointPow.lean#L16-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolyGermPointPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalSmulOfIsHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolyGermPointPow
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
open MvPolynomial Topology Filter Asymptotics
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolyGermPointPow

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolyGermPointPow_coeff_eq_zero_of_isBigO_a896a5b521ef {P : Polynomial ℂ} {k : ℕ}
    (h : (fun t => P.eval t) =O[𝓝 0] fun t : ℂ => ‖t‖ ^ k) : ∀ d < k, P.coeff d = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«PolyGermPointPow».«coeff_eq_zero_of_isBigO» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolyGermPointPow_coeff_eq_zero_of_isBigO_a896a5b521ef
