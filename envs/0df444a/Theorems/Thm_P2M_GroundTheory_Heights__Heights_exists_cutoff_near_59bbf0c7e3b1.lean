-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_cutoff_near_59bbf0c7e3b1
-- name    : P2M_GroundTheory_Heights__Heights_exists_cutoff_near_59bbf0c7e3b1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:34:11.709978+00:00
-- url     : https://prove2.me/theorems/9d728ec5-b141-406e-9555-6170609ed553
-- title:
--   P2 M Ground Theory Heights  Heights exists cutoff near 59bbf0c7e3b1: P2 M Ground Theory Heights  Heights exists cutoff near 59bbf0c7e3b1
-- statement:
--   The P2 M Ground Theory Heights  Heights exists cutoff near 59bbf0c7e3b1 construction uses the P2 M Ground Theory Heights  Heights exists cutoff near 59bbf0c7e3b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/CutOffNear.lean#L10-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/CutOffNear.lean#L10-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CutOffNear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Set Topology MvPolynomial ComplexSets
open scoped ContDiff Manifold

theorem P2M_GroundTheory_Heights__Heights_exists_cutoff_near_59bbf0c7e3b1 {n : ℕ} {S U : Set (Fin n → ℂ)} (hS : IsClosed S) (hU : IsOpen U)
    (hSU : S ⊆ U) :
    ∃ χ : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ tsupport χ ⊆ U ∧
      ∃ V : Set (Fin n → ℂ), IsOpen V ∧ S ⊆ V ∧ ∀ x ∈ V, χ x = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_cutoff_near» := P2M_GroundTheory_Heights__Heights_exists_cutoff_near_59bbf0c7e3b1
