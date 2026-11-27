-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_le_volume_ellipsoidR
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.le_volume_ellipsoidR
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:27:57.086323+00:00
-- url     : https://prove2.me/theorems/ad172e09-094c-4375-99f7-0ab7f11ab21e
-- title:
--   Geometry Of Numbers Theory: le volume ellipsoid R
-- statement:
--   The Geometry Of Numbers Theory construction uses the le volume ellipsoid R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/EllipsoidSt.lean#L218-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/EllipsoidSt.lean#L218-L244

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_EllipsoidStA
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_EllipsoidSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Matrix
open scoped ComplexOrder MatrixOrder
open ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall

theorem ReciprocityTheory.GeometryOfNumbersTheory.le_volume_ellipsoidR {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) {R : ℝ}
    (hR : 0 < R) :
    (2 * R / Real.sqrt r) ^ r / Real.sqrt G.det ≤
      (volume {y : Fin r → ℝ | qR G y ≤ R ^ 2}).toReal := by sorry
