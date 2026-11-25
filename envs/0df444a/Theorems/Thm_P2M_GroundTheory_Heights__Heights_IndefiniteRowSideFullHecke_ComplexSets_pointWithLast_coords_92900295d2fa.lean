-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pointWithLast_coords_92900295d2fa
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pointWithLast_coords_92900295d2fa
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:08.805689+00:00
-- url     : https://prove2.me/theorems/0160e56a-1db4-4047-bd89-128ba7243d59
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets point With Last coords 92900295d2fa: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets poi
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets point With Last coords 92900295d2fa construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets point With Last coords 92900295d2fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermWeierstrassPreparation.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermWeierstrassPreparation.lean#L23-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassPreparation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParametricCircleIntegralAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCircleArgumentPrinciple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPowerSumsEsymmAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermWeierstrassPreparation
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
open Topology Filter Metric Complex Real
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pointWithLast_coords_92900295d2fa {σ : Type} (x : Option σ → ℂ) :
    pointWithLast (fun i => x (some i)) (x none) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«pointWithLast_coords» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pointWithLast_coords_92900295d2fa
