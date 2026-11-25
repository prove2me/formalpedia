-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_gramSt_hadamard
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.gramSt_hadamard
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:53:58.005198+00:00
-- url     : https://prove2.me/theorems/37f898a9-ecd8-4196-ab04-32a278340cf2
-- title:
--   Geometry Of Numbers Theory: gram St hadamard
-- statement:
--   The Geometry Of Numbers Theory construction uses the gram St hadamard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/GramSt.lean#L119-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/GramSt.lean#L119-L132

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.gramSt_hadamard {k : ℕ} {D : Matrix (Fin k) (Fin k) ℂ} (hD : D.PosDef) :
    D.det.re ≤ ∏ j : Fin k, (D j j).re := by sorry
