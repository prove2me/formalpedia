-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_inj
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:31:28.607679+00:00
-- url     : https://prove2.me/theorems/e55db2f0-46a4-47cc-9315-0197a9fd4b9d
-- title:
--   Tor: gm inj
-- statement:
--   The Tor construction uses the gm inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RosVal.lean#L22-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RosVal.lean#L22-L46

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_inj {X Z : Scheme.{0}} (κ : Z ⟶ X) [IsOpenImmersion κ] (z : Z) {U U' : X.Opens} (h : κ z ∈ U) (h' : κ z ∈ U')
    {a : Γ(X, U)ˣ} {b : Γ(X, U')ˣ} (e : gm κ z U a = gm κ z U' b) :
    gm (𝟙 X) (κ z) U a = gm (𝟙 X) (κ z) U' b := by sorry
