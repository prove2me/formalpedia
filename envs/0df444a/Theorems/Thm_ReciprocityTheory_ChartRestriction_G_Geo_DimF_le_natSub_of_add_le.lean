-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_le_natSub_of_add_le
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.DimF.le_natSub_of_add_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:12.498093+00:00
-- url     : https://prove2.me/theorems/45c03143-5dd9-4653-8df8-f7931c33bd1d
-- title:
--   Dim F: le nat Sub of add le
-- statement:
--   The Dim F construction uses the le nat Sub of add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAA.lean#L91-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAA.lean#L91-L96

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.DimF.le_natSub_of_add_le {k n : ℕ} {x : ℕ∞} (h : (k : ℕ∞) + x ≤ n) : x ≤ ((n - k : ℕ) : ℕ∞) := by sorry
