-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isoPullId_maps
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.isoPullId_maps
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:53.621801+00:00
-- url     : https://prove2.me/theorems/783d6f58-4c17-48d5-93ff-59729d2637a9
-- title:
--   Tor: iso Pull Id maps
-- statement:
--   The Tor construction uses the iso Pull Id maps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/CocycleIdentityIso.lean#L138-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/CocycleIdentityIso.lean#L138-L175

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.isoPullId_maps {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L' L : RigLB G} {w : LB.Iso L'.L L.L}
    (hm : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L'.rig L.rig)
    {F : G.left ⟶ G.left} (hF : F = 𝟙 _) {e : (𝟙_ (Over S)).left ⟶ (𝟙_ (Over S)).left} (he₀ : e = 𝟙 _)
    (he : eSec G ≫ F = e ≫ eSec G) :
    LB.Gen.Maps (LB.linCombIso (isoPullId w hF) (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L'.rig
      (rigPullOf F e he L.L L.rig) := by sorry
