-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_monoNormSq_le_one
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.monoNormSq_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:20.442919+00:00
-- url     : https://prove2.me/theorems/aad9dbc5-96eb-4460-8388-57b9ddd3a9b0
-- title:
--   Geometry Of Numbers Theory: mono Norm Sq le one
-- statement:
--   The Geometry Of Numbers Theory construction uses the mono Norm Sq le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L25-L33

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.monoNormSq_le_one {D : ℕ} (a : Fin (D + 1) → ℕ) : monoNormSq a ≤ 1 := by sorry
