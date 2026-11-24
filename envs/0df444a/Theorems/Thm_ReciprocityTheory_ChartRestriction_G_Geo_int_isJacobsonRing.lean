-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_int_isJacobsonRing
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.int_isJacobsonRing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:18.089189+00:00
-- url     : https://prove2.me/theorems/d971e7b9-5d6b-4d0a-b91c-872e13edf2dd
-- title:
--   Geo: int is Jacobson Ring
-- statement:
--   The Geo construction uses the int is Jacobson Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodA.lean#L51-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodA.lean#L51-L63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open Ideal

theorem ReciprocityTheory.ChartRestriction.G.Geo.int_isJacobsonRing : IsJacobsonRing ℤ := by sorry
