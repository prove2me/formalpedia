-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_GlobalFunctionsDvrOpen_eq_zero_of_mul
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen.eq_zero_of_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:23:06.106488+00:00
-- url     : https://prove2.me/theorems/c7877203-33ab-5905-8fa8-911e1e1b6dcd
-- title:
--   Global Functions Dvr Open: eq zero of mul
-- statement:
--   The Global Functions Dvr Open construction uses the eq zero of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/GlobalFunctionsDvrOpen.lean#L40-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/GlobalFunctionsDvrOpen.lean#L40-L66

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen.eq_zero_of_mul {X : Scheme.{0}} (p : X ⟶ Sp V) [Flat p] {r : V} (hr : r ≠ 0) (f : Γ(X, ⊤))
    (h : p.appTop ((Scheme.ΓSpecIso (CommRingCat.of V)).inv r) * f = 0) : f = 0 := by sorry
