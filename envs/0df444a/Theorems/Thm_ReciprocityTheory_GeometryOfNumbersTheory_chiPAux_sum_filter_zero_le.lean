-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_sum_filter_zero_le
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_sum_filter_zero_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:53:37.257941+00:00
-- url     : https://prove2.me/theorems/08c93436-cff3-53a1-b376-ca512bab2f16
-- title:
--   Geometry Of Numbers Theory: chi PAux sum filter zero le
-- statement:
--   The Geometry Of Numbers Theory construction uses the chi PAux sum filter zero le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L353-L392
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L353-L392

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Finset

theorem ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_sum_filter_zero_le (D n : ℕ) (hn : 1 ≤ n) (P : ℝ) (hP : 0 ≤ P)
    (hb : ∀ b ∈ (Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0),
      -Real.log (monoNormSq b) ≤ (2 + (D : ℝ)) * n * P) :
    ∑ b ∈ (Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0),
      -Real.log (monoNormSq b) ≤ 3 ^ D * (2 + (D : ℝ)) * P * (n : ℝ) ^ D := by sorry
