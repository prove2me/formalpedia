-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_gramSt_det_re_le_of_sub
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.gramSt_det_re_le_of_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:19:48.852182+00:00
-- url     : https://prove2.me/theorems/3c24751e-ac27-4c9c-976e-0be6e5785b02
-- title:
--   Geometry Of Numbers Theory: gram St det re le of sub
-- statement:
--   The Geometry Of Numbers Theory construction uses the gram St det re le of sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/GramSt.lean#L30-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/GramSt.lean#L30-L60

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.gramSt_det_re_le_of_sub {G H : Matrix ι ι ℂ} (hG : G.PosDef)
    (hGH : (H - G).PosSemidef) : G.det.re ≤ H.det.re := by sorry
