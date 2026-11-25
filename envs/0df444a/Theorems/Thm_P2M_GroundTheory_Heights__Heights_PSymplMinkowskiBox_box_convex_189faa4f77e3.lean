-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplMinkowskiBox_box_convex_189faa4f77e3
-- name    : P2M_GroundTheory_Heights__Heights_PSymplMinkowskiBox_box_convex_189faa4f77e3
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:36.104323+00:00
-- url     : https://prove2.me/theorems/511ebc8a-1103-4d35-ac6b-822a913d7782
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Minkowski Box box convex 189faa4f77e3: P2 M Ground Theory Heights  Heights PSympl Minkowski Box box convex 189faa4f77e3
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Minkowski Box box convex 189faa4f77e3 construction uses the P2 M Ground Theory Heights  Heights PSympl Minkowski Box box convex 189faa4f77e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplMinkowskiBox.lean#L17-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplMinkowskiBox.lean#L17-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplMinkowskiBox
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
open Matrix MeasureTheory
open GroundTheory.Heights₂.Heights.PSymplMinkowskiBox

theorem P2M_GroundTheory_Heights__Heights_PSymplMinkowskiBox_box_convex_189faa4f77e3 {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (a : ι → ℝ) :
    Convex ℝ {x : ι → ℝ | ∀ i, |(A *ᵥ x) i| < a i} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplMinkowskiBox».«box_convex» := P2M_GroundTheory_Heights__Heights_PSymplMinkowskiBox_box_convex_189faa4f77e3
