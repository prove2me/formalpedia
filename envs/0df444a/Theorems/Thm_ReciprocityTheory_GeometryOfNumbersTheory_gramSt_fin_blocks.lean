-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_gramSt_fin_blocks
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.gramSt_fin_blocks
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:19:48.529802+00:00
-- url     : https://prove2.me/theorems/1fedbccb-da50-4c05-897d-bc41e6008d9c
-- title:
--   Geometry Of Numbers Theory: gram St fin blocks
-- statement:
--   The Geometry Of Numbers Theory construction uses the gram St fin blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/GramSt.lean#L104-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/GramSt.lean#L104-L117

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.gramSt_fin_blocks {a b : ℕ} {M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ} (hM : M.PosDef) :
    M.det.re ≤ (M.submatrix (Fin.castAdd b) (Fin.castAdd b)).det.re *
      (M.submatrix (Fin.natAdd a) (Fin.natAdd a)).det.re := by sorry
