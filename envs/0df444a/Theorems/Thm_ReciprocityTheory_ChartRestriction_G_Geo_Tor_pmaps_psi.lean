-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pmaps_psi
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.pmaps_psi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:58.613801+00:00
-- url     : https://prove2.me/theorems/9ebbf75c-9ab0-40a5-ba50-1dc6b571a3b0
-- title:
--   Tor: pmaps psi
-- statement:
--   The Tor construction uses the pmaps psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RigIsoCongr.lean#L21-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RigIsoCongr.lean#L21-L80

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1600000

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.pmaps_psi {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {g : R →+* R'} {D : Out.DegPre R}
    {D' : Out.DegPre R'} (hD : Out.IsPullDeg g D D') (F : Type) [Field F] [Algebra (FractionRing R) F]
    [Algebra (FractionRing R') F]
    (hj : Out.jFK (R := R') F ≫ Out.jK R' ≫ spMap g = Out.jFK (R := R) F ≫ Out.jK R) (x : D'.X) :
    PMaps hD.w (K := PUnit) (fun _ => Out.jFK (R := R') F ≫ D'.xK x) (fun _ => Out.jFK (R := R) F ≫ D.xK (hD.xe x))
      (fun _ => -1) (LB.pullGen _ _ _ (D'.psi x) (Out.jFK (R := R') F))
      (LB.pullGen _ _ _ (D.psi (hD.xe x)) (Out.jFK (R := R) F)) (𝟙 _) := by sorry
