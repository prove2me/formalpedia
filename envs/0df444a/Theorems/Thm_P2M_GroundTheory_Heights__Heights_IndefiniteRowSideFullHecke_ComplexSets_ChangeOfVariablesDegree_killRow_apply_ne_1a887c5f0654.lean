-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_killRow_apply_ne_1a887c5f0654
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_killRow_apply_ne_1a887c5f0654
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:46.077025+00:00
-- url     : https://prove2.me/theorems/e1c302cf-06dd-45b3-8666-c26b799e9722
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Change Of Variables Degree kill Row apply ne 1a887c5f0654: P2 M Ground Theory Heights  Heights Indefinite Row Side Full
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Change Of Variables Degree kill Row apply ne 1a887c5f0654 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Change Of Variables Degree kill Row apply ne 1a887c5f0654 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChangeOfVariablesDegreePiola.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChangeOfVariablesDegreePiola.lean#L57-L59

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_killRow_apply_ne_1a887c5f0654 {i k : Fin n} (h : k ≠ i) (M : Fin n → Fin n → ℝ) :
    killRow i M k = M k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«ChangeOfVariablesDegree».«killRow_apply_ne» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_killRow_apply_ne_1a887c5f0654
