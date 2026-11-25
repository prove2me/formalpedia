-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_BrouwerFixedPoint_smooth_of_changeOfVariablesDegree_1b6ab2a0e304
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_BrouwerFixedPoint_smooth_of_changeOfVariablesDegree_1b6ab2a0e304
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:19:07.127533+00:00
-- url     : https://prove2.me/theorems/e9f949bf-482e-5b1d-abdb-810426c4e21d
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Brouwer Fixed Point smooth of change Of Variables Degree 1b6ab2a0e304: P2 M Ground Theory Heights  Heights Indefinite Ro
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Brouwer Fixed Point smooth of change Of Variables Degree 1b6ab2a0e304 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Brouwer Fixed Point smooth of change Of Variables Degree 1b6ab2a0e304 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBrouwerFixedPoint.lean#L11-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBrouwerFixedPoint.lean#L11-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBrouwerFixedPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChangeOfVariablesDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBrouwerFixedPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped ContDiff
open Metric
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_BrouwerFixedPoint_smooth_of_changeOfVariablesDegree_1b6ab2a0e304
    (hL : ChangeOfVariablesDegree.Statement) (n : ℕ) (g : (Fin n → ℝ) → Fin n → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgb : ∀ x, ‖g x‖ ≤ 1) : ∃ x, g x = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«BrouwerFixedPoint».«smooth_of_changeOfVariablesDegree» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_BrouwerFixedPoint_smooth_of_changeOfVariablesDegree_1b6ab2a0e304
