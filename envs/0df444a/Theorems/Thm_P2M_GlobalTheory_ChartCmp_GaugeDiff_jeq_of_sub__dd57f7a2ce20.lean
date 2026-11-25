-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ChartCmp_GaugeDiff_jeq_of_sub__dd57f7a2ce20
-- name    : P2M_GlobalTheory_ChartCmp_GaugeDiff_jeq_of_sub__dd57f7a2ce20
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:38:00.227409+00:00
-- url     : https://prove2.me/theorems/c98e3952-951d-4167-907a-319514786a7f
-- title:
--   P2 M Global Theory Chart Cmp Gauge Diff jeq of sub  dd57f7a2ce20: P2 M Global Theory Chart Cmp Gauge Diff jeq of sub  dd57f7a2ce20
-- statement:
--   The P2 M Global Theory Chart Cmp Gauge Diff jeq of sub  dd57f7a2ce20 construction uses the P2 M Global Theory Chart Cmp Gauge Diff jeq of sub  dd57f7a2ce20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonicalGaugeDifferenceBiadditiveJet.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonicalGaugeDifferenceBiadditiveJet.lean#L75-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetEqFormalExpIffAndExistsLog
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalChartJetRelUnitOneOnAxes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonicalGaugeDifferenceBiadditiveJet
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (transF IsInvPair)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open MvPowerSeries
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.GaugeDiff
variable {k : Type} [CommRing k] {d : ℕ}

theorem P2M_GlobalTheory_ChartCmp_GaugeDiff_jeq_of_sub__dd57f7a2ce20 {σ : Type} {m : ℕ} {f g u v : MvPowerSeries σ k} (h : JEq m f g) (e : u - v = g - f) :
    JEq m u v := by sorry

alias «GlobalTheory».«ChartCmp».«GaugeDiff».«jeq_of_sub'» := P2M_GlobalTheory_ChartCmp_GaugeDiff_jeq_of_sub__dd57f7a2ce20
