-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_maps_pt
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_maps_pt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:26.634973+00:00
-- url     : https://prove2.me/theorems/c9179c9b-d4c3-4801-9378-caeeff1196ad
-- title:
--   Tor: gm maps pt
-- statement:
--   The Tor construction uses the gm maps pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/CocycleIdentityIso.lean#L101-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/CocycleIdentityIso.lean#L101-L123

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AdmissibleBasePowerSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleIdentityIso
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
variable {X : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_maps_pt {L' L : LB X} {w : LB.Iso L' L} {Y : Scheme.{0}} {φ : Y ⟶ X} {a : LB.Gen (L'.pull φ)}
    {b : LB.Gen (L.pull φ)} (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => φ) (fun _ => 1)) a b)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (p : L.ι) (q : L'.ι) (hp : φ (r z) ∈ L.U p) (hq : φ (r z) ∈ L'.U q) :
    gm r z _ (b.s (fun _ => p)) = gv w (r ≫ φ) z p q * gm r z _ (a.s (fun _ => q)) := by sorry
