-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_hasCompactSupport_comp_sub_6ff964a89034
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_hasCompactSupport_comp_sub_6ff964a89034
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:53.260832+00:00
-- url     : https://prove2.me/theorems/0d7066bf-a442-4420-802d-8e092c1c3617
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Change Of Variables Degree has Compact Support comp sub 6ff964a89034: P2 M Ground Theory Heights  Heights Indefinite Row
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Change Of Variables Degree has Compact Support comp sub 6ff964a89034 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Change Of Variables Degree has Compact Support comp sub 6ff964a89034 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChangeOfVariablesDegree.lean#L21-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChangeOfVariablesDegree.lean#L21-L36

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_hasCompactSupport_comp_sub_6ff964a89034 {n : ℕ} (φ : (Fin n → ℝ) → Fin n → ℝ) (C : ℝ)
    (hC : ∀ x, ‖φ x - x‖ ≤ C) (g : (Fin n → ℝ) → ℝ) (hgc : HasCompactSupport g)
    (y₀ : Fin n → ℝ) : HasCompactSupport fun x => g (φ x - y₀) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«ChangeOfVariablesDegree».«hasCompactSupport_comp_sub» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_hasCompactSupport_comp_sub_6ff964a89034
