-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NonIsolatedFibreCurve_analyticOnNhd_of_differentiableOn_c00fe3584ee6
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NonIsolatedFibreCurve_analyticOnNhd_of_differentiableOn_c00fe3584ee6
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:20:25.497997+00:00
-- url     : https://prove2.me/theorems/50b0bc16-5a40-4626-8a0d-17a50b14db85
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Non Isolated Fibre Curve analytic On Nhd of differentiable On c00fe3584ee6: P2 M Ground Theory Heights  Heights Indefini
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Non Isolated Fibre Curve analytic On Nhd of differentiable On c00fe3584ee6 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Non Isolated Fibre Curve analytic On Nhd of differentiable On c00fe3584ee6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNonIsolatedFibreCurve.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNonIsolatedFibreCurve.lean#L12-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNonIsolatedFibreCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNonIsolatedFibreCurve
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
open Topology Metric Filter

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NonIsolatedFibreCurve_analyticOnNhd_of_differentiableOn_c00fe3584ee6 {k : ℕ} {O : Set (Fin k → ℂ)}
    {g : (Fin k → ℂ) → ℂ} (hO : IsOpen O) (hg : DifferentiableOn ℂ g O) : AnalyticOnNhd ℂ g O := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«NonIsolatedFibreCurve».«analyticOnNhd_of_differentiableOn» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NonIsolatedFibreCurve_analyticOnNhd_of_differentiableOn_c00fe3584ee6
