-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_det_update_eq_sum_10ad24af5154
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_det_update_eq_sum_10ad24af5154
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:07.701812+00:00
-- url     : https://prove2.me/theorems/4aecbda5-ac3c-4cd4-9ac7-112320ed1847
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Change Of Variables Degree det update eq sum 10ad24af5154: P2 M Ground Theory Heights  Heights Indefinite Row Side Full
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Change Of Variables Degree det update eq sum 10ad24af5154 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Change Of Variables Degree det update eq sum 10ad24af5154 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChangeOfVariablesDegreePiola.lean#L35-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChangeOfVariablesDegreePiola.lean#L35-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChangeOfVariablesDegreePiola
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
open MeasureTheory
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_det_update_eq_sum_10ad24af5154 (V : Fin n → Fin n → ℝ) (k : Fin n) (r : Fin n → ℝ) :
    Matrix.det (Matrix.of (Function.update V k r)) =
      ∑ l, r l * Matrix.det (Matrix.of (Function.update V k (Pi.single l 1))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«ChangeOfVariablesDegree».«det_update_eq_sum» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_det_update_eq_sum_10ad24af5154
