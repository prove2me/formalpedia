-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_neg_log_det_le
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.neg_log_det_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:29:55.409204+00:00
-- url     : https://prove2.me/theorems/58d3894b-3b94-46b6-bcb4-aa20836a9484
-- title:
--   Geometry Of Numbers Theory: neg log det le
-- statement:
--   The Geometry Of Numbers Theory construction uses the neg log det le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/HadZSt.lean#L9-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/HadZSt.lean#L9-L90

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_GramSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_HadZStA
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_HadZSt
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
open scoped ComplexOrder

theorem ReciprocityTheory.GeometryOfNumbersTheory.neg_log_det_le {r' r : ℕ} (hr : r' ≤ r) {G' : Matrix (Fin r') (Fin r') ℂ}
    {G : Matrix (Fin r) (Fin r) ℂ} (hG' : G'.PosDef) (hG : G.PosDef)
    (M : Matrix (Fin r) (Fin r') ℤ) (hM : Function.Injective (M.map (Int.cast : ℤ → ℚ)).mulVec)
    (N : Matrix (Fin r) (Fin r) ℤ) (hN : N.det ≠ 0) {A lam : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hnorm : (((A : ℂ) ^ 2) • G' -
      (M.map (Int.cast : ℤ → ℂ))ᴴ * G * M.map (Int.cast : ℤ → ℂ)).PosSemidef)
    (hsmall : ∀ i, (((N.map (Int.cast : ℤ → ℂ))ᴴ * G * N.map (Int.cast : ℤ → ℂ)) i i).re ≤ lam ^ 2) :
    -(1 / 2) * Real.log G'.det.re ≤
      -(1 / 2) * Real.log G.det.re + r' * Real.log A + ((r : ℝ) - r') * Real.log lam := by sorry
