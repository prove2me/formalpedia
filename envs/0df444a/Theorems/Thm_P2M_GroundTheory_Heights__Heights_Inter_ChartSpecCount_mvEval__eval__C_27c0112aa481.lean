-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartSpecCount_mvEval__eval__C_27c0112aa481
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ChartSpecCount_mvEval__eval__C_27c0112aa481
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:08.340276+00:00
-- url     : https://prove2.me/theorems/2e2d94ba-6e91-4d86-9bf6-f403b9fbf665
-- title:
--   P2 M Ground Theory Heights  Heights Inter Chart Spec Count mv Eval  eval  C 27c0112aa481: P2 M Ground Theory Heights  Heights Inter Chart Spec Count mv Eval  eval  C 27c0112aa481
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Chart Spec Count mv Eval  eval  C 27c0112aa481 construction uses the P2 M Ground Theory Heights  Heights Inter Chart Spec Count mv Eval  eval  C 27c0112aa481 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartSpecCount.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartSpecCount.lean#L43-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartPrimElt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocAwaySpec
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartSpecCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartSpecCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open Polynomial
open GroundTheory.Heights₂.Heights.Inter.ChartSpecCount

theorem P2M_GroundTheory_Heights__Heights_Inter_ChartSpecCount_mvEval__eval__C_27c0112aa481 {A K Q : Type*} [CommRing A] [CommRing K] (k : A →+* K) (y : Q → K)
    (τ : MvPolynomial Q A) (p : A[X]) :
    MvPolynomial.eval₂ k y (p.eval₂ MvPolynomial.C τ) = p.eval₂ k (MvPolynomial.eval₂ k y τ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ChartSpecCount».«mvEval₂_eval₂_C» := P2M_GroundTheory_Heights__Heights_Inter_ChartSpecCount_mvEval__eval__C_27c0112aa481
