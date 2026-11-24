-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_MultiHomogZ_weight_blkWtZ
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.MultiHomogZ.weight_blkWtZ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:39.382948+00:00
-- url     : https://prove2.me/theorems/63e4ad3b-a11d-4126-8b04-e79e34b3416f
-- title:
--   Multi Homog Z: weight blk Wt Z
-- statement:
--   The Multi Homog Z construction uses the weight blk Wt Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterMinorA.lean#L17-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterMinorA.lean#L17-L25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterMinorA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.MultiHomogZ
open MvPolynomial
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]

theorem ReciprocityTheory.ChartRestriction.G.Geo.MultiHomogZ.weight_blkWtZ (k : K) (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (blkWtZ (ι := ι) k) m = ∑ i, (m ⟨k, i⟩ : ℤ) := by sorry
