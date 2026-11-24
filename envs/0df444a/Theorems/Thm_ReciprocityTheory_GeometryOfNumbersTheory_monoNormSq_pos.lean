-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_monoNormSq_pos
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.monoNormSq_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:12.484311+00:00
-- url     : https://prove2.me/theorems/e89512cf-b264-4afb-8e77-7ad7e381c466
-- title:
--   Geometry Of Numbers Theory: mono Norm Sq pos
-- statement:
--   The Geometry Of Numbers Theory construction uses the mono Norm Sq pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L7-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L7-L13

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.monoNormSq_pos {D : ℕ} (a : Fin (D + 1) → ℕ) : 0 < monoNormSq a := by sorry
