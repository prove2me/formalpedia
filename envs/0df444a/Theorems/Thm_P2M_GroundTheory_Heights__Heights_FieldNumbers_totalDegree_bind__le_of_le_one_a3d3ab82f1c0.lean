-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_totalDegree_bind__le_of_le_one_a3d3ab82f1c0
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_totalDegree_bind__le_of_le_one_a3d3ab82f1c0
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:17:58.343628+00:00
-- url     : https://prove2.me/theorems/8292bc9d-1552-4e48-b5ae-c5b12ec59321
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers total Degree bind  le of le one a3d3ab82f1c0: P2 M Ground Theory Heights  Heights Field Numbers total Degree bind  le of le one a3d3ab82f1c0
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers total Degree bind  le of le one a3d3ab82f1c0 construction uses the P2 M Ground Theory Heights  Heights Field Numbers total Degree bind  le of le one a3d3ab82f1c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PEventuallyPolyShift.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PEventuallyPolyShift.lean#L11-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PEventuallyPolyShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial Filter
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_totalDegree_bind__le_of_le_one_a3d3ab82f1c0 {σ τ R : Type*} [CommSemiring R]
    (f : σ → MvPolynomial τ R) (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial σ R) :
    (bind₁ f p).totalDegree ≤ p.totalDegree := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«totalDegree_bind₁_le_of_le_one» := P2M_GroundTheory_Heights__Heights_FieldNumbers_totalDegree_bind__le_of_le_one_a3d3ab82f1c0
