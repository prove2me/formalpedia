-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAtEval_apply_40b5f84f59da
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAtEval_apply_40b5f84f59da
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:02.101595+00:00
-- url     : https://prove2.me/theorems/163a0f85-3ace-4df1-b4e4-5f04cde9ffb2
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets analytic At Eval apply 40b5f84f59da: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets ana
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets analytic At Eval apply 40b5f84f59da construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets analytic At Eval apply 40b5f84f59da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/DetEqZeroOfMulVecEqZero.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/DetEqZeroOfMulVecEqZero.lean#L39-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_DetEqZeroOfMulVecEqZero
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
open Topology Filter Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAtEval_apply_40b5f84f59da {σ : Type} [Fintype σ] (p y : σ → ℂ) (g : analyticAtSubring p) :
    analyticAtEval p y g = (g : (σ → ℂ) → ℂ) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«analyticAtEval_apply» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAtEval_apply_40b5f84f59da

attribute [defeq] P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAtEval_apply_40b5f84f59da
