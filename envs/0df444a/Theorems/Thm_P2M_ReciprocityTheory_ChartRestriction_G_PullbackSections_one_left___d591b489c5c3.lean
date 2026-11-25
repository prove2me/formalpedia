-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_one_left___d591b489c5c3
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_one_left___d591b489c5c3
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T17:58:46.853802+00:00
-- url     : https://prove2.me/theorems/387da055-444b-5bde-a2dd-57a530a21b7b
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Pullback Sections one left   d591b489c5c3: P2 M Reciprocity Theory Chart Restriction G Pullback Sections one left   d591b489c5c3
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Pullback Sections one left   d591b489c5c3 construction uses the P2 M Reciprocity Theory Chart Restriction G Pullback Sections one left   d591b489c5c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnChartX.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnChartX.lean#L19-L23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnChartX
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_one_left___d591b489c5c3 {T : Scheme.{0}} {X : Over T} {M : Over T} [GrpObj M] :
    (1 : X ⟶ M).left = X.hom ≫ η[M].left := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«PullbackSections».«one_left''» := P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_one_left___d591b489c5c3
