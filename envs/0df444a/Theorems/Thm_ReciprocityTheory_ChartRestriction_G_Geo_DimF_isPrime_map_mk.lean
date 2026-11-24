-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_isPrime_map_mk
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.DimF.isPrime_map_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:56.734576+00:00
-- url     : https://prove2.me/theorems/3056e419-a9a3-4dc9-b156-5cafe66d1801
-- title:
--   Dim F: is Prime map mk
-- statement:
--   The Dim F construction uses the is Prime map mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAA.lean#L9-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAA.lean#L9-L11

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.DimF
variable {A : Type*} [CommRing A]

theorem ReciprocityTheory.ChartRestriction.G.Geo.DimF.isPrime_map_mk {q M : Ideal A} [M.IsPrime] (h : q ≤ M) :
    (M.map (Ideal.Quotient.mk q)).IsPrime := by sorry
