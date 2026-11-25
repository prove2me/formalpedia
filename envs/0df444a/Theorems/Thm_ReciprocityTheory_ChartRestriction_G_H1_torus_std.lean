-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_torus_std
-- name    : ReciprocityTheory.ChartRestriction.G.H1.torus_std
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:26:37.488168+00:00
-- url     : https://prove2.me/theorems/fc880263-18d9-5893-a122-f302a16ec95f
-- title:
--   H1: torus std
-- statement:
--   The H1 construction uses the torus std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/DimSplitPf.lean#L14-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/DimSplitPf.lean#L14-L64

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

theorem ReciprocityTheory.ChartRestriction.G.H1.torus_std (A X : Type) [CommRing A] [Nontrivial A] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    Algebra.IsStandardSmoothOfRelativeDimension (Module.finrank ℤ X) A (AddMonoidAlgebra A X) := by sorry
