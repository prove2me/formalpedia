-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_good
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:33:56.481324+00:00
-- url     : https://prove2.me/theorems/135a923f-b4f8-4304-8dc8-d7e5b753174d
-- title:
--   Tor: exists good
-- statement:
--   The Tor construction uses the exists good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ValCalc.lean#L68-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ValCalc.lean#L68-L86

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
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
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Y' Z : Scheme.{0}}
variable (L : LB X)

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_good (hL : L.IsLB) (z : Z) {K : Type} (ψ : K → (Z ⟶ X)) (j : K → L.ι)
    (hc : ∀ a b, ψ a = ψ b → j a = j b) (hj : ∀ k, ψ k z ∈ L.U (j k)) :
    ∃ J, Good L z J ∧ ∀ k, J (ψ k) = j k := by sorry
