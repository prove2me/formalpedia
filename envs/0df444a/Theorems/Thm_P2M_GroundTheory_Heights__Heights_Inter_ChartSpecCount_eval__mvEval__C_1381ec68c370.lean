-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartSpecCount_eval__mvEval__C_1381ec68c370
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ChartSpecCount_eval__mvEval__C_1381ec68c370
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:08.951801+00:00
-- url     : https://prove2.me/theorems/78682c85-b619-4ef1-a109-99a43e7aa45c
-- title:
--   P2 M Ground Theory Heights  Heights Inter Chart Spec Count eval  mv Eval  C 1381ec68c370: P2 M Ground Theory Heights  Heights Inter Chart Spec Count eval  mv Eval  C 1381ec68c370
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Chart Spec Count eval  mv Eval  C 1381ec68c370 construction uses the P2 M Ground Theory Heights  Heights Inter Chart Spec Count eval  mv Eval  C 1381ec68c370 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartSpecCount.lean#L35-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartSpecCount.lean#L35-L41

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ChartSpecCount_eval__mvEval__C_1381ec68c370 {A K Q : Type*} [CommRing A] [CommRing K] (k : A →+* K) (x : K) (G : Q → A[X])
    (F : MvPolynomial Q A) :
    (MvPolynomial.eval₂ C G F).eval₂ k x = MvPolynomial.eval₂ k (fun q => (G q).eval₂ k x) F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ChartSpecCount».«eval₂_mvEval₂_C» := P2M_GroundTheory_Heights__Heights_Inter_ChartSpecCount_eval__mvEval__C_1381ec68c370
