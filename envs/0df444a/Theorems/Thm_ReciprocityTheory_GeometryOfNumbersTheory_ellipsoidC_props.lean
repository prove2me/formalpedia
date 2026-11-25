-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_ellipsoidC_props
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.ellipsoidC_props
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:27:21.543086+00:00
-- url     : https://prove2.me/theorems/97dbc55c-99f6-5bba-9b3a-e0035340bbc4
-- title:
--   Geometry Of Numbers Theory: ellipsoid C props
-- statement:
--   The Geometry Of Numbers Theory construction uses the ellipsoid C props property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/EllipsoidSt.lean#L123-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/EllipsoidSt.lean#L123-L127

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.ellipsoidC_props {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) (R : ℝ) :
    Convex ℝ {y | qC G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qC G y ≤ R ^ 2}, -y ∈ {y | qC G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qC G y ≤ R ^ 2} ∧ MeasurableSet {y | qC G y ≤ R ^ 2} := by sorry
