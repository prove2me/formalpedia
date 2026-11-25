-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_sum_split
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_sum_split
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:53:47.793896+00:00
-- url     : https://prove2.me/theorems/4c64ea2c-f6ce-5f0f-8f18-f27eb8925bb5
-- title:
--   Geometry Of Numbers Theory: chi PAux sum split
-- statement:
--   The Geometry Of Numbers Theory construction uses the chi PAux sum split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L171-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L171-L209

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_sum_split (D n : ℕ) (g : (Fin (D + 1) → ℕ) → ℝ) :
    ∑ b ∈ Finset.Nat.antidiagonalTuple (D + 1) (n + 1), g b =
      ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, g (Function.update a 0 (a 0 + 1)) +
      ∑ b ∈ (Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0), g b := by sorry
