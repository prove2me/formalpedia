-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_regVert_eq_of_le_height_one
-- name    : ReciprocityTheory.ChartRestriction.G.T0.regVert_eq_of_le_height_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:31:30.664802+00:00
-- url     : https://prove2.me/theorems/e7c3ab26-58ee-45a2-834a-7e919f3d0ed1
-- title:
--   T0: reg Vert eq of le height one
-- statement:
--   The T0 construction uses the reg Vert eq of le height one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/RegVert.lean#L8-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/RegVert.lean#L8-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegAVpt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegVert
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open IsLocalRing

theorem ReciprocityTheory.ChartRestriction.G.T0.regVert_eq_of_le_height_one {A : Type*} [CommRing A] [IsDomain A] {Q P : Ideal A} [Q.IsPrime]
    [P.IsPrime] (hQ : Q ≠ ⊥) (hQP : Q ≤ P) (hP : P.height = 1) : Q = P := by sorry
