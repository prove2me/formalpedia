-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_le_monoNormSq
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.le_monoNormSq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:53:06.787655+00:00
-- url     : https://prove2.me/theorems/8dc7cde6-9116-5bea-a36e-44e7ef213066
-- title:
--   Geometry Of Numbers Theory: le mono Norm Sq
-- statement:
--   The Geometry Of Numbers Theory construction uses the le mono Norm Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L82-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L82-L88

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.le_monoNormSq {D : ℕ} (a : Fin (D + 1) → ℕ) :
    (((D + 1 : ℝ) ^ (∑ i, a i)) * ((∑ i, a i : ℕ) + D : ℝ) ^ D)⁻¹ ≤ monoNormSq a := by sorry
