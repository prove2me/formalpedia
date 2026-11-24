-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_card_adt_le
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_card_adt_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:15.742145+00:00
-- url     : https://prove2.me/theorems/957cbe6d-77af-4dcb-9fc7-d645dc3a02ea
-- title:
--   Geometry Of Numbers Theory: chi PAux card adt le
-- statement:
--   The Geometry Of Numbers Theory construction uses the chi PAux card adt le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L125-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L125-L146

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_card_adt_le (k m : ℕ) : (Finset.Nat.antidiagonalTuple (k + 1) m).card ≤ (m + 1) ^ k := by sorry
