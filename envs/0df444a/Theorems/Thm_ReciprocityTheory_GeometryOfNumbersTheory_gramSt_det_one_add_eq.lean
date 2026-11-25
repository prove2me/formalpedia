-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_gramSt_det_one_add_eq
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.gramSt_det_one_add_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:53:54.662548+00:00
-- url     : https://prove2.me/theorems/104b5be2-cd0a-4b1f-b486-d9581653eee0
-- title:
--   Geometry Of Numbers Theory: gram St det one add eq
-- statement:
--   The Geometry Of Numbers Theory construction uses the gram St det one add eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/GramSt.lean#L12-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/GramSt.lean#L12-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_GramSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Matrix
open scoped ComplexOrder MatrixOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ReciprocityTheory.GeometryOfNumbersTheory.gramSt_det_one_add_eq {Q : Matrix ι ι ℂ} (hQ : Q.PosSemidef) :
    (1 + Q).det = ((∏ i, (1 + hQ.1.eigenvalues i) : ℝ) : ℂ) := by sorry
