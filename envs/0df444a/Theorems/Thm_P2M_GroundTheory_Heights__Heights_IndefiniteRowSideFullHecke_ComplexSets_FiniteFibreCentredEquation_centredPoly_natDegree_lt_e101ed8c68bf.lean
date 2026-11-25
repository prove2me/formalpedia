-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteFibreCentredEquation_centredPoly_natDegree_lt_e101ed8c68bf
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteFibreCentredEquation_centredPoly_natDegree_lt_e101ed8c68bf
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:20:17.468805+00:00
-- url     : https://prove2.me/theorems/421035cf-d5df-4677-921f-0ab38b68738c
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Finite Fibre Centred Equation centred Poly nat Degree lt e101ed8c68bf: P2 M Ground Theory Heights  Heights Indefinite Ro
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Finite Fibre Centred Equation centred Poly nat Degree lt e101ed8c68bf construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Finite Fibre Centred Equation centred Poly nat Degree lt e101ed8c68bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteFibreCentredEquation.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteFibreCentredEquation.lean#L23-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreCentredEquation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreGermIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassPreparation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteFibreCentredEquation
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
open Topology Filter Polynomial

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteFibreCentredEquation_centredPoly_natDegree_lt_e101ed8c68bf (a : ℂ) {k : ℕ} (c : Fin k → ℂ) :
    (FiniteFibreCentredEquation.centredPoly a c).natDegree < k + 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«FiniteFibreCentredEquation».«centredPoly_natDegree_lt» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteFibreCentredEquation_centredPoly_natDegree_lt_e101ed8c68bf
