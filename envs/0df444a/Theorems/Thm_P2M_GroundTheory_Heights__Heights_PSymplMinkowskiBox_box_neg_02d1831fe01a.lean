-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplMinkowskiBox_box_neg_02d1831fe01a
-- name    : P2M_GroundTheory_Heights__Heights_PSymplMinkowskiBox_box_neg_02d1831fe01a
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:15:09.431204+00:00
-- url     : https://prove2.me/theorems/afa3dfa0-9029-4662-b5ff-0719dd5d6fd6
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Minkowski Box box neg 02d1831fe01a: P2 M Ground Theory Heights  Heights PSympl Minkowski Box box neg 02d1831fe01a
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Minkowski Box box neg 02d1831fe01a construction uses the P2 M Ground Theory Heights  Heights PSympl Minkowski Box box neg 02d1831fe01a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplMinkowskiBox.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplMinkowskiBox.lean#L11-L15

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

theorem P2M_GroundTheory_Heights__Heights_PSymplMinkowskiBox_box_neg_02d1831fe01a {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (a : ι → ℝ) (x : ι → ℝ)
    (hx : ∀ i, |(A *ᵥ x) i| < a i) : ∀ i, |(A *ᵥ (-x)) i| < a i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplMinkowskiBox».«box_neg» := P2M_GroundTheory_Heights__Heights_PSymplMinkowskiBox_box_neg_02d1831fe01a
