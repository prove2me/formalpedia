-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_cutoff_near_zeroSet_710ba7aa020d
-- name    : P2M_GroundTheory_Heights__Heights_exists_cutoff_near_zeroSet_710ba7aa020d
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:46:02.099135+00:00
-- url     : https://prove2.me/theorems/8ed575b2-c8e9-4dec-93b4-5087e8df920e
-- title:
--   P2 M Ground Theory Heights  Heights exists cutoff near zero Set 710ba7aa020d: P2 M Ground Theory Heights  Heights exists cutoff near zero Set 710ba7aa020d
-- statement:
--   The P2 M Ground Theory Heights  Heights exists cutoff near zero Set 710ba7aa020d construction uses the P2 M Ground Theory Heights  Heights exists cutoff near zero Set 710ba7aa020d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/CutOffNear.lean#L24-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/CutOffNear.lean#L24-L33

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

theorem P2M_GroundTheory_Heights__Heights_exists_cutoff_near_zeroSet_710ba7aa020d {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hIU : zeroSet I ⊆ U) :
    ∃ χ : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ tsupport χ ⊆ U ∧
      ∃ V : Set (Fin n → ℂ), IsOpen V ∧ zeroSet I ⊆ V ∧ ∀ x ∈ V, χ x = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_cutoff_near_zeroSet» := P2M_GroundTheory_Heights__Heights_exists_cutoff_near_zeroSet_710ba7aa020d
