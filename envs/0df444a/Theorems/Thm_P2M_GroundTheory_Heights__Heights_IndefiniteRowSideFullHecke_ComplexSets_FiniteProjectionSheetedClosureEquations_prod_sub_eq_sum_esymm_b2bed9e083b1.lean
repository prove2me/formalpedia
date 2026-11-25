-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteProjectionSheetedClosureEquations_prod_sub_eq_sum_esymm_b2bed9e083b1
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteProjectionSheetedClosureEquations_prod_sub_eq_sum_esymm_b2bed9e083b1
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:38.327726+00:00
-- url     : https://prove2.me/theorems/73a09589-4a08-4840-ae87-634c90c7bc65
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Finite Projection Sheeted Closure Equations prod sub eq sum esymm b2bed9e083b1: P2 M Ground Theory Heights  Heights Inde
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Finite Projection Sheeted Closure Equations prod sub eq sum esymm b2bed9e083b1 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Finite Projection Sheeted Closure Equations prod sub eq sum esymm b2bed9e083b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteProjectionSheetedClosureEquations.lean#L36-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteProjectionSheetedClosureEquations.lean#L36-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionSheetedClosureEquations
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionProperBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperSheetedFibreEsymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGridProductLowerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionSheetedClosureEquations
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteProjectionSheetedClosureEquations_prod_sub_eq_sum_esymm_b2bed9e083b1 (m : Multiset ℂ) (a : ℂ) :
    (m.map fun x => a - x).prod =
      ∑ j ∈ Finset.range (Multiset.card m + 1), (-1) ^ j * m.esymm j * a ^ (Multiset.card m - j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«FiniteProjectionSheetedClosureEquations».«prod_sub_eq_sum_esymm» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteProjectionSheetedClosureEquations_prod_sub_eq_sum_esymm_b2bed9e083b1
