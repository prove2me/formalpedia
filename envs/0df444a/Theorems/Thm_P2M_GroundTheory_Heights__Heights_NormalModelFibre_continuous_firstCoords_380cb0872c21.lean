-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalModelFibre_continuous_firstCoords_380cb0872c21
-- name    : P2M_GroundTheory_Heights__Heights_NormalModelFibre_continuous_firstCoords_380cb0872c21
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:04:53.456857+00:00
-- url     : https://prove2.me/theorems/0f4b846b-5a94-460c-a757-fa3892f1b554
-- title:
--   P2 M Ground Theory Heights  Heights Normal Model Fibre continuous first Coords 380cb0872c21: P2 M Ground Theory Heights  Heights Normal Model Fibre continuous first Coords 380cb0872c21
-- statement:
--   The P2 M Ground Theory Heights  Heights Normal Model Fibre continuous first Coords 380cb0872c21 construction uses the P2 M Ground Theory Heights  Heights Normal Model Fibre continuous first Coords 380cb0872c21 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/NormalModelFibreNear.lean#L68-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/NormalModelFibreNear.lean#L68-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PModelLocalizationMaximalPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_NormalModelFibreNear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology ComplexSets Metric
noncomputable section
open GroundTheory.Heights₂.Heights.NormalModelFibre
variable {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)

theorem P2M_GroundTheory_Heights__Heights_NormalModelFibre_continuous_firstCoords_380cb0872c21 : Continuous (IndefiniteRowSideFullHecke.ComplexSets.firstCoords (n := n) (m := M.m)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalModelFibre».«continuous_firstCoords» := P2M_GroundTheory_Heights__Heights_NormalModelFibre_continuous_firstCoords_380cb0872c21
