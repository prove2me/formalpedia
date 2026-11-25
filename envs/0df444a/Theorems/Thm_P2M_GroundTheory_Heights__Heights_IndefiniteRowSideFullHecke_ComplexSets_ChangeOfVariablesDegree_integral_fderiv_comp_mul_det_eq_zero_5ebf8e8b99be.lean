-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_integral_fderiv_comp_mul_det_eq_zero_5ebf8e8b99be
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_integral_fderiv_comp_mul_det_eq_zero_5ebf8e8b99be
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:19:43.123716+00:00
-- url     : https://prove2.me/theorems/be66e40f-8bc6-4eb7-b4e9-8c5a380f843f
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Change Of Variables Degree integral fderiv comp mul det eq zero 5ebf8e8b99be: P2 M Ground Theory Heights  Heights Indefi
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Change Of Variables Degree integral fderiv comp mul det eq zero 5ebf8e8b99be construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Change Of Variables Degree integral fderiv comp mul det eq zero 5ebf8e8b99be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChangeOfVariablesDegree.lean#L47-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChangeOfVariablesDegree.lean#L47-L90

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChangeOfVariablesDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChangeOfVariablesDegreePiola
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChangeOfVariablesDegree
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
open MeasureTheory Metric
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
variable {m : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_integral_fderiv_comp_mul_det_eq_zero_5ebf8e8b99be (φ : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hu : HasCompactSupport fun x => φ x - x)
    (g : (Fin (m + 1) → ℝ) → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∫ x, fderiv ℝ g (φ x) (Pi.single 0 1) * (fderiv ℝ φ x).det = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«ChangeOfVariablesDegree».«integral_fderiv_comp_mul_det_eq_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_integral_fderiv_comp_mul_det_eq_zero_5ebf8e8b99be
