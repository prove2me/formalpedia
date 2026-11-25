-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_act_mul_apply
-- name    : ReciprocityTheory.ChartRestriction.G.H1.act_mul_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:45:50.440928+00:00
-- url     : https://prove2.me/theorems/c7b41359-75aa-4a67-9868-688aa6e71909
-- title:
--   H1: act mul apply
-- statement:
--   The H1 construction uses the act mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/AlphaPair.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/AlphaPair.lean#L35-L36

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_AlphaPair
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
  CartesianMonoidalCategory MonObj IsLocalRing NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S}
variable {O : Type} [Ring O] (ρ : RingAct A O)

theorem ReciprocityTheory.ChartRestriction.G.H1.act_mul_apply (x : T ⟶ A) (a b : O) : x ≫ ρ.act (a * b) = (x ≫ ρ.act b) ≫ ρ.act a := by sorry
