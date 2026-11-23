-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_IsPullUnifPre_toIsPullUnif
-- name    : ReciprocityTheory.ChartRestriction.G.Out.IsPullUnifPre.toIsPullUnif
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:27:16.598808+00:00
-- url     : https://prove2.me/theorems/04eee14e-3e85-44cf-90b4-3a37e207e2e8
-- title:
--   Is Pull Unif Pre: to Is Pull Unif
-- statement:
--   The Is Pull Unif Pre construction uses the to Is Pull Unif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/UnifBaseChangeInjOfSeamsCS.lean#L66-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/UnifBaseChangeInjOfSeamsCS.lean#L66-L75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_UnifBaseChangeInjOfSeamsCS
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out
open Semi
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem ReciprocityTheory.ChartRestriction.G.Out.IsPullUnifPre.toIsPullUnif {I : Ideal R} {I' : Ideal R'} {φ : R →+* R'} {D : DegData R I}
    {D' : DegData R' I'} {hD : IsPullDeg φ D.toPre D'.toPre}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {A' : PolAV (Spec (CommRingCat.of (FractionRing R')))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
    {bc : G' ≅ (Over.pullback (specOf φ)).obj G}
    {U : Unif I D A G} {U' : Unif I' D' A' G'}
    (h : IsPullUnifPre φ hD bc U.toUnifPre U'.toUnifPre) : IsPullUnif φ hD bc U U' := by sorry
