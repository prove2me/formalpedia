-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_GlobalFunctionsDvrOpen_appTop_fst_injective
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen.appTop_fst_injective
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:23:15.295529+00:00
-- url     : https://prove2.me/theorems/4f34901b-e84c-5ec4-b7df-8493ba133dd8
-- title:
--   Global Functions Dvr Open: app Top fst injective
-- statement:
--   The Global Functions Dvr Open construction uses the app Top fst injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/GlobalFunctionsDvrOpen.lean#L77-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/GlobalFunctionsDvrOpen.lean#L77-L102

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobFnsDvr
import Definitions.Def_Lemmata_GeneralBFactFurther_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobalFunctionsDvrOpen
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen
variable {V : Type} [CommRing V] [IsDomain V]

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen.appTop_fst_injective [IsDiscreteValuationRing V] {X : Scheme.{0}} (p : X ⟶ Sp V) [Flat p]
    [QuasiCompact p] [QuasiSeparated p] :
    haveI := isOpenImmersion_frac (IsDiscreteValuationRing.exists_irreducible V).choose_spec
    Function.Injective (pullback.fst p (spMap (algebraMap V (FractionRing V)))).appTop := by sorry
