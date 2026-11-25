-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_varInt_fsPot_9f8a08547c5c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_varInt_fsPot_9f8a08547c5c
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:21:46.477319+00:00
-- url     : https://prove2.me/theorems/a89ef033-37c3-4dce-8aee-5fdce79b739e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets var Int fs Pot 9f8a08547c5c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets var Int fs
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets var Int fs Pot 9f8a08547c5c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets var Int fs Pot 9f8a08547c5c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PlaneIdealTwoOne.lean#L83-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PlaneIdealTwoOne.lean#L83-L103

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PlaneIdealTwoOne
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
open MvPolynomial MeasureTheory
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_varInt_fsPot_9f8a08547c5c {n : ℕ} (h : GroundTheory.Heights₂.Heights.HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (f : (Fin n → ℂ) → ℝ) :
    GroundTheory.Heights₂.Heights.varInt J 1 f (fun _ => fsPot h) =
      2 * GroundTheory.Heights₂.Heights.varInt J 1 f (fun _ y => Real.log (h.dualNorm y)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«varInt_fsPot» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_varInt_fsPot_9f8a08547c5c
