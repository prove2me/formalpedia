-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_exists_chiP_le
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.exists_chiP_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:53:26.7871+00:00
-- url     : https://prove2.me/theorems/b95d17d1-d222-4dcd-9f9e-557b941a6cce
-- title:
--   Geometry Of Numbers Theory: exists chi P le
-- statement:
--   The Geometry Of Numbers Theory construction uses the exists chi P le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L289-L351
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L289-L351

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.exists_chiP_le (D : ℕ) : ∃ C : ℝ, ∀ n : ℕ, chiP D n ≤ C * (n : ℝ) ^ (D + 1) := by sorry
