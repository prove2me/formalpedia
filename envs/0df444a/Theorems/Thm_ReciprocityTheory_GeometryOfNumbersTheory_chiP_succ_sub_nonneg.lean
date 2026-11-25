-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiP_succ_sub_nonneg
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.chiP_succ_sub_nonneg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:53:57.896748+00:00
-- url     : https://prove2.me/theorems/72a45008-e81f-41f2-a64f-7f1c2ac28255
-- title:
--   Geometry Of Numbers Theory: chi P succ sub nonneg
-- statement:
--   The Geometry Of Numbers Theory construction uses the chi P succ sub nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L279-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L279-L287

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.chiP_succ_sub_nonneg (D n : ℕ) : 0 ≤ chiP D (n + 1) - chiP D n := by sorry
