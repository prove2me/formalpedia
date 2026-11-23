-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_pw
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_pw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:19.032429+00:00
-- url     : https://prove2.me/theorems/db33d042-5605-4f2c-b348-2b41d24c58bf
-- title:
--   Tor: exists pw
-- statement:
--   The Tor construction uses the exists pw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsMonHomOfMul.lean#L50-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsMonHomOfMul.lean#L50-L65

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_pw (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (p : K → L.ι) (q : K → L'.ι) :
    ∃ u : Γ(Y, LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q → gm r z _ u = pw w φ' ε r z p q := by sorry
