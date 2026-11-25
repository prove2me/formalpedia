-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_t_act
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_t_act
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:14:52.47142+00:00
-- url     : https://prove2.me/theorems/c98edecb-2a16-453d-9b8b-8e9fa9ac4b05
-- title:
--   Tor: val t act
-- statement:
--   The Tor construction uses the val t act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/GtPtsVal.lean#L123-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/GtPtsVal.lean#L123-L131

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GtPtsTor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GtPtsVal
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_t_act (χ : D.X) {W : Scheme.{0}} (w : W ⟶ (WeightPf.Te D I e ⊗ thickObj R I e G).left) (z : W)
    {J : (W ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) :
    val (g.t χ) (w ≫ (WeightPf.act g).left) z J =
      gm (w ≫ (fst (WeightPf.Te D I e) (thickObj R I e G)).left) z ⊤ (charUnit _ D.X χ) *
        val (g.t χ) (w ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)).left) z J := by sorry
