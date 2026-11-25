-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_MultiHomogZ_isWeightedHomogeneous_blkWtZ
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.MultiHomogZ.isWeightedHomogeneous_blkWtZ
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:22:57.986863+00:00
-- url     : https://prove2.me/theorems/999a3a90-9feb-4c4a-83d3-0ad0e8159d82
-- title:
--   Multi Homog Z: is Weighted Homogeneous blk Wt Z
-- statement:
--   The Multi Homog Z construction uses the is Weighted Homogeneous blk Wt Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterMinorA.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterMinorA.lean#L27-L32

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.MultiHomogZ.isWeightedHomogeneous_blkWtZ {f : MRingOver R ι} {a : K → ℕ} (h : IsMultiHomog f a)
    (k : K) : IsWeightedHomogeneous (blkWtZ (ι := ι) k) f (a k : ℤ) := by sorry
