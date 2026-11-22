-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_rigIso_congr
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.rigIso_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:39:33.493396+00:00
-- url     : https://prove2.me/theorems/cfd7612d-0f67-4cb2-9c2b-93468d3a4ea5
-- title:
--   Tor: rig Iso congr
-- statement:
--   The Tor construction uses the rig Iso congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RigIsoCongr.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RigIsoCongr.lean#L11-L18

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.rigIso_congr {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {LG PP : RigLB G} (hL : LG = PP) {PP' : RigLB G'} (m : CubeMap G' G) {c : CubicalStr G PP}
    {c' : CubicalStr G' PP'} (h : m.IsPullCubical c' c) {F : G'.left ⟶ G.left} (hF : F = m.F) {e : S' ⟶ S}
    (he : e = m.e) : ∃ (w : LB.Iso PP'.L (LG.L.pull F)) (h₀ : eSec G' ≫ F = e ≫ eSec G), w.IsGen ∧
      LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) PP'.rig (rigPullOf F e h₀ LG.L LG.rig) := by sorry
