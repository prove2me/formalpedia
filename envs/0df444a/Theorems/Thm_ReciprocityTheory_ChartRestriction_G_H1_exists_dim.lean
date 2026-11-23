-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_exists_dim
-- name    : ReciprocityTheory.ChartRestriction.G.H1.exists_dim
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:45.990869+00:00
-- url     : https://prove2.me/theorems/bb4d11fa-5e37-410c-9c82-6f8fea55d60c
-- title:
--   H1: exists dim
-- statement:
--   The H1 construction uses the exists dim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/DimSplitPf.lean#L95-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/DimSplitPf.lean#L95-L110

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

theorem ReciprocityTheory.ChartRestriction.G.H1.exists_dim {X Y : Scheme.{0}} (f : X ⟶ Y) [Smooth f] (x : X) :
    ∃ (n : ℕ) (W : X.Opens), x ∈ W ∧ SmoothOfRelativeDimension n (W.ι ≫ f) := by sorry
