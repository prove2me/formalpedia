-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_GlobalFunctionsDvrOpen_restrict_basicOpen_injective
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen.restrict_basicOpen_injective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:28:20.058797+00:00
-- url     : https://prove2.me/theorems/269afd70-b96b-51d7-9dc5-83e720449654
-- title:
--   Global Functions Dvr Open: restrict basic Open injective
-- statement:
--   The Global Functions Dvr Open construction uses the restrict basic Open injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/GlobalFunctionsDvrOpen.lean#L68-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/GlobalFunctionsDvrOpen.lean#L68-L75

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen.restrict_basicOpen_injective {X : Scheme.{0}} [CompactSpace X] [QuasiSeparatedSpace X]
    (s : Γ(X, ⊤)) (hs : ∀ f : Γ(X, ⊤), s * f = 0 → f = 0) :
    Function.Injective (X.presheaf.map (homOfLE (le_top : X.basicOpen s ≤ ⊤)).op) := by sorry
