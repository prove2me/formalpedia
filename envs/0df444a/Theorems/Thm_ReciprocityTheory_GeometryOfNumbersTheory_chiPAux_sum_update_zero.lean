-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_sum_update_zero
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_sum_update_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:11.02244+00:00
-- url     : https://prove2.me/theorems/b3a7e665-22c1-421c-b411-333ffeb86b2c
-- title:
--   Geometry Of Numbers Theory: chi PAux sum update zero
-- statement:
--   The Geometry Of Numbers Theory construction uses the chi PAux sum update zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L90-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L90-L93

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_sum_update_zero {D : ℕ} (a : Fin (D + 1) → ℕ) (v : ℕ) :
    ∑ i, Function.update a 0 v i = v + ∑ i : Fin D, a i.succ := by sorry
