-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_lastToCoordinate_coordinateToLast_6599e7c66a76
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_lastToCoordinate_coordinateToLast_6599e7c66a76
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:21:21.798808+00:00
-- url     : https://prove2.me/theorems/c2f8d400-49df-488c-9e3e-0cde90232f20
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets last To Coordinate coordinate To Last 6599e7c66a76: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke C
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets last To Coordinate coordinate To Last 6599e7c66a76 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets last To Coordinate coordinate To Last 6599e7c66a76 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PWeierstrassDivisionAtPoint.lean#L35-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PWeierstrassDivisionAtPoint.lean#L35-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeierstrassDivisionAtPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PWeierstrassDivisionAtPoint
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
noncomputable section
variable {τ : Type} [DecidableEq τ]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_lastToCoordinate_coordinateToLast_6599e7c66a76 (c : τ) (y : τ → ℂ) :
    lastToCoordinate c (coordinateToLast c y) = y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«lastToCoordinate_coordinateToLast» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_lastToCoordinate_coordinateToLast_6599e7c66a76
