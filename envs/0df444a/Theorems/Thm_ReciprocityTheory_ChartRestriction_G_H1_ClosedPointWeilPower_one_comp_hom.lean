-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_ClosedPointWeilPower_one_comp_hom
-- name    : ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower.one_comp_hom
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:25:52.859607+00:00
-- url     : https://prove2.me/theorems/f44c3d13-b24e-540b-991f-c8ac5a773fbf
-- title:
--   Closed Point Weil Power: one comp hom
-- statement:
--   The Closed Point Weil Power construction uses the one comp hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/ClosedPointWeilPower.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/ClosedPointWeilPower.lean#L22-L24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ClosedPointWeilPower
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S}

theorem ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower.one_comp_hom (f : A ⟶ A) (hf : IsMonHom f) : (1 : T ⟶ A) ≫ f = 1 := by sorry
