-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_GlobalFunctionsDvrGeneric_powObj_props
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrGeneric.powObj_props
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:23:00.316266+00:00
-- url     : https://prove2.me/theorems/fd2c64c4-07a7-553d-a46a-277d4532b207
-- title:
--   Global Functions Dvr Generic: pow Obj props
-- statement:
--   The Global Functions Dvr Generic construction uses the pow Obj props property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/GlobalFunctionsDvrGeneric.lean#L15-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/GlobalFunctionsDvrGeneric.lean#L15-L30

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrGeneric.powObj_props {S : Scheme.{0}} (G : Over S) [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] :
    ∀ n : ℕ, Smooth (powObj G n).hom ∧ IsSeparated (powObj G n).hom ∧ QuasiCompact (powObj G n).hom
  := by sorry
