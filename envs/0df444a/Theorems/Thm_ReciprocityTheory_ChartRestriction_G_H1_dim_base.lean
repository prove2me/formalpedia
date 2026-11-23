-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_dim_base
-- name    : ReciprocityTheory.ChartRestriction.G.H1.dim_base
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:54.430704+00:00
-- url     : https://prove2.me/theorems/27f0b378-29af-4234-8e47-f63bd5a55ac0
-- title:
--   H1: dim base
-- statement:
--   The H1 construction uses the dim base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/DimSplitPf.lean#L112-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/DimSplitPf.lean#L112-L118

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem ReciprocityTheory.ChartRestriction.G.H1.dim_base {X S X' S' : Scheme.{0}} {f : X ⟶ S} {f' : X' ⟶ S'} {a : X' ⟶ X} {b : S' ⟶ S} (h : IsPullback a f' f b)
    {n m : ℕ} {W : X.Opens} (hW : SmoothOfRelativeDimension n (W.ι ≫ f)) (hm : SmoothOfRelativeDimension m f') (x : X')
    (hx : a x ∈ W) : n = m := by sorry
