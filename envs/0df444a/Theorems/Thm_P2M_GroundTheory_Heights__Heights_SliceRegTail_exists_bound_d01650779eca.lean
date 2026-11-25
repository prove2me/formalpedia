-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceRegTail_exists_bound_d01650779eca
-- name    : P2M_GroundTheory_Heights__Heights_SliceRegTail_exists_bound_d01650779eca
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:38:32.828797+00:00
-- url     : https://prove2.me/theorems/3bc92b5f-9540-4418-b703-6b199249794f
-- title:
--   P2 M Ground Theory Heights  Heights Slice Reg Tail exists bound d01650779eca: P2 M Ground Theory Heights  Heights Slice Reg Tail exists bound d01650779eca
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Reg Tail exists bound d01650779eca construction uses the P2 M Ground Theory Heights  Heights Slice Reg Tail exists bound d01650779eca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceRegTail.lean#L12-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceRegTail.lean#L12-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegVarBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegTailMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutTailMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceRegTail
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
open MvPolynomial Filter Topology Matrix ComplexSets

theorem P2M_GroundTheory_Heights__Heights_SliceRegTail_exists_bound_d01650779eca {n : ℕ} {a : (Fin n → ℂ) → ℝ}
    (ha : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → a (t • x) = a x) (hac : ContinuousOn a {x | x ≠ 0}) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, |a x| ≤ C := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceRegTail».«exists_bound» := P2M_GroundTheory_Heights__Heights_SliceRegTail_exists_bound_d01650779eca
