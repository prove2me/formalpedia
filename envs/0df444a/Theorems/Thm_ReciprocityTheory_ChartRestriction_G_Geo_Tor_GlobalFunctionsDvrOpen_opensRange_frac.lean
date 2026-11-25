-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_GlobalFunctionsDvrOpen_opensRange_frac
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen.opensRange_frac
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:27:24.9917+00:00
-- url     : https://prove2.me/theorems/f020b47a-661f-589b-b52a-f5e5dbe664fa
-- title:
--   Global Functions Dvr Open: opens Range frac
-- statement:
--   The Global Functions Dvr Open construction uses the opens Range frac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/GlobalFunctionsDvrOpen.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/GlobalFunctionsDvrOpen.lean#L31-L38

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen.opensRange_frac [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ) :
    haveI := isOpenImmersion_frac hϖ
    (spMap (algebraMap V (FractionRing V))).opensRange =
      (Sp V).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of V)).inv ϖ) := by sorry
