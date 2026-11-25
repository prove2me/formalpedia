-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_GlobalFunctionsDvrGeneric_appTop_spMap
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrGeneric.appTop_spMap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:23:12.189023+00:00
-- url     : https://prove2.me/theorems/6d372131-08c2-57ab-aed9-cc408ff4bf03
-- title:
--   Global Functions Dvr Generic: app Top sp Map
-- statement:
--   The Global Functions Dvr Generic construction uses the app Top sp Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/GlobalFunctionsDvrGeneric.lean#L34-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/GlobalFunctionsDvrGeneric.lean#L34-L42

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobalFunctionsDvrOpen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobalFunctionsDvrGeneric
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrGeneric
open ReciprocityTheory.ChartRestriction.G.Out
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrGeneric.appTop_spMap (v : V) :
    (spMap (algebraMap V (FractionRing V))).appTop ((Scheme.ΓSpecIso (CommRingCat.of V)).inv v) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv (algebraMap V (FractionRing V) v) := by sorry
