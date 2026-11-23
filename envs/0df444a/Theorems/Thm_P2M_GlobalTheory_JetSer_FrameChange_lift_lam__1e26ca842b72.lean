-- Prove2me | Theorems.Thm_P2M_GlobalTheory_JetSer_FrameChange_lift_lam__1e26ca842b72
-- name    : P2M_GlobalTheory_JetSer_FrameChange_lift_lam__1e26ca842b72
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:23:39.98075+00:00
-- url     : https://prove2.me/theorems/21dd3cf7-2087-4954-aba5-b7be229c26e9
-- title:
--   P2 M Global Theory Jet Ser Frame Change lift lam  1e26ca842b72: P2 M Global Theory Jet Ser Frame Change lift lam  1e26ca842b72
-- statement:
--   The P2 M Global Theory Jet Ser Frame Change lift lam  1e26ca842b72 construction uses the P2 M Global Theory Jet Ser Frame Change lift lam  1e26ca842b72 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EvalStandardPointsThree.lean#L110-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EvalStandardPointsThree.lean#L110-L118

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

theorem P2M_GlobalTheory_JetSer_FrameChange_lift_lam__1e26ca842b72 {T : Over S} (x y : T ⟶ G) (k : Fin 4) :
    (lift x y).left ≫ lamφ G k = ((![x * y, x, y, 1] : Fin 4 → (T ⟶ G)) k).left := by sorry

alias «GlobalTheory».«JetSer».«FrameChange».«lift_lamφ» := P2M_GlobalTheory_JetSer_FrameChange_lift_lam__1e26ca842b72
