-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ChartCmp_FrameRatio_comp_psum__249d30ba0974
-- name    : P2M_GlobalTheory_ChartCmp_FrameRatio_comp_psum__249d30ba0974
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:38:00.171948+00:00
-- url     : https://prove2.me/theorems/e163ffe3-ef85-4fed-8ce2-ae90b868530c
-- title:
--   P2 M Global Theory Chart Cmp Frame Ratio comp psum  249d30ba0974: P2 M Global Theory Chart Cmp Frame Ratio comp psum  249d30ba0974
-- statement:
--   The P2 M Global Theory Chart Cmp Frame Ratio comp psum  249d30ba0974 construction uses the P2 M Global Theory Chart Cmp Frame Ratio comp psum  249d30ba0974 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JetFramesDifferByUnitEachOrder.lean#L30-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JetFramesDifferByUnitEachOrder.lean#L30-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetFramesDifferByUnitEachOrder
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.FrameRatio

theorem P2M_GlobalTheory_ChartCmp_FrameRatio_comp_psum__249d30ba0974 {S : Scheme.{0}} (G : Over S) [GrpObj G] {T T' : Over S} (f : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) : f ≫ psum G x I = psum G (fun k => f ≫ x k) I := by sorry

alias «GlobalTheory».«ChartCmp».«FrameRatio».«comp_psum'» := P2M_GlobalTheory_ChartCmp_FrameRatio_comp_psum__249d30ba0974
