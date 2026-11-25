-- Prove2me | Theorems.Thm_P2M_GlobalTheory_JetSer_FrameChange_cub_lam__899c0adc3157
-- name    : P2M_GlobalTheory_JetSer_FrameChange_cub_lam__899c0adc3157
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:07:26.551879+00:00
-- url     : https://prove2.me/theorems/e7417a0b-076e-4a34-acb9-e798d7f7a81a
-- title:
--   P2 M Global Theory Jet Ser Frame Change cub lam  899c0adc3157: P2 M Global Theory Jet Ser Frame Change cub lam  899c0adc3157
-- statement:
--   The P2 M Global Theory Jet Ser Frame Change cub lam  899c0adc3157 construction uses the P2 M Global Theory Jet Ser Frame Change cub lam  899c0adc3157 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EvalStandardPointsThree.lean#L165-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EvalStandardPointsThree.lean#L165-L172

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EvalStandardPointsThree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε)
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer GlobalTheory.JetSer.FrameChange
variable {S : Scheme.{0}} (G : Over S) [GrpObj G]
variable {G}
variable [IsCommMonObj G]

theorem P2M_GlobalTheory_JetSer_FrameChange_cub_lam__899c0adc3157 {T : Over S} (x x' y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) (t : U) :
    t * lamV h x (x' * y) =
      (∏ I : thK, h ((lift x (lift x' y)).left ≫ thφ G (x3 G) I) ^ thε I) * t * (lamV h x x' * lamV h x y) := by sorry

alias «GlobalTheory».«JetSer».«FrameChange».«cub_lam₂» := P2M_GlobalTheory_JetSer_FrameChange_cub_lam__899c0adc3157
