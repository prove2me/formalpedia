-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.sval_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:28:56.099994+00:00
-- url     : https://prove2.me/theorems/7c05c489-0ef6-41f7-b391-adbab56447f6
-- title:
--   Tor: sval of
-- statement:
--   The Tor construction uses the sval of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ValCalc.lean#L105-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ValCalc.lean#L105-L109

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
variable {L} {K K' : Type} [Fintype K] [Fintype K']

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.sval_of {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ X) → L.ι) (j : K → L.ι) (h : ∀ k, J (r ≫ φ k) = j k) :
    sval s r z J = gs r z (LB.wchart L φ j) (s.f j) := by sorry
