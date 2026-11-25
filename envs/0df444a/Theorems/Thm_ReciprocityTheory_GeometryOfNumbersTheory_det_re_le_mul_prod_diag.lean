-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_det_re_le_mul_prod_diag
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.det_re_le_mul_prod_diag
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:52:49.688351+00:00
-- url     : https://prove2.me/theorems/fa6b0a7c-94db-58a4-919b-d9f7594bccc6
-- title:
--   Geometry Of Numbers Theory: det re le mul prod diag
-- statement:
--   The Geometry Of Numbers Theory construction uses the det re le mul prod diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/GramSt.lean#L143-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/GramSt.lean#L143-L151

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.det_re_le_mul_prod_diag {a b : ℕ} {M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ}
    (hM : M.PosDef) :
    M.det.re ≤ (M.submatrix (Fin.castAdd b) (Fin.castAdd b)).det.re *
      ∏ j : Fin b, (M (Fin.natAdd a j) (Fin.natAdd a j)).re := by sorry
