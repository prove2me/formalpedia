-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_LocalResidues_gs_const
-- name    : ReciprocityTheory.ChartRestriction.G.H1.LocalResidues.gs_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:24:13.929391+00:00
-- url     : https://prove2.me/theorems/c1246a33-a7f5-46d3-8994-993b56a93381
-- title:
--   Local Residues: gs const
-- statement:
--   The Local Residues construction uses the gs const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/LocalResidues.lean#L38-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/LocalResidues.lean#L38-L54

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_JetApproximation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_LocalResidues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.LocalResidues
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {k : Type} [Field k] {X W Z : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.H1.LocalResidues.gs_const {Y' : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) (q : X ⟶ Y') (e : Y' ⟶ Spec (CommRingCat.of k))
    [IsIso e] (hq : q ≫ e = p) (y : X) (a : Γ(Y', ⊤)) : ∃ c : k, gs q y ⊤ a = kappa p y c := by sorry
