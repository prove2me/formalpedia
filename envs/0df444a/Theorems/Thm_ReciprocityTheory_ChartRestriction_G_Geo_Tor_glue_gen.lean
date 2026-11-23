-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_gen
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.glue_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:21.271806+00:00
-- url     : https://prove2.me/theorems/ddb5702b-2751-4c77-8b3e-74a1101af273
-- title:
--   Tor: glue gen
-- statement:
--   The Tor construction uses the glue gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RosVal.lean#L56-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RosVal.lean#L56-L125

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.glue_gen {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    {ι' : Type} (W : ι' → Y.Opens) (hW : ∀ y, ∃ s, y ∈ W s)
    (t : ∀ s, LB.Gen (LB.LinComb M (fun k => (W s).ι ≫ φ k) ε)) (ht : ∀ s, (t s).IsGen)
    (agree : ∀ s s' (Z : Scheme.{0}) (r : Z ⟶ (W s).toScheme) (r' : Z ⟶ (W s').toScheme) (z : Z) (J), Good M z J →
      r ≫ (W s).ι = r' ≫ (W s').ι → val (t s) r z J = val (t s') r' z J) :
    ∃ u : LB.Gen (LB.LinComb M φ ε), u.IsGen ∧ ∀ s (Z : Scheme.{0}) (r : Z ⟶ (W s).toScheme) (z : Z) (J), Good M z J →
      val u (r ≫ (W s).ι) z J = val (t s) r z J := by sorry
