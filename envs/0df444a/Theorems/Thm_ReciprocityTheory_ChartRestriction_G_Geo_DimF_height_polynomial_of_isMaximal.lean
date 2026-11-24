-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_height_polynomial_of_isMaximal
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_polynomial_of_isMaximal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:12.163727+00:00
-- url     : https://prove2.me/theorems/d7968da2-735c-4de6-9f98-e766436b2316
-- title:
--   Dim F: height polynomial of is Maximal
-- statement:
--   The Dim F construction uses the height polynomial of is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAC.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAC.lean#L9-L17

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
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
open Ideal

theorem ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_polynomial_of_isMaximal {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsJacobsonRing R] {c : ℕ∞} (hR : ∀ m : Ideal R, m.IsMaximal → m.height = c)
    (M : Ideal (Polynomial R)) (hM : M.IsMaximal) : M.height = c + 1 := by sorry
