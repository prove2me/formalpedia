-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SharpGradient_sharpAt_sum__57325bd9992d
-- name    : P2M_GlobalTheory_SharpGradient_sharpAt_sum__57325bd9992d
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:38:01.407241+00:00
-- url     : https://prove2.me/theorems/46d256fc-d044-4d85-bdf0-c5011687ba20
-- title:
--   P2 M Global Theory Sharp Gradient sharp At sum  57325bd9992d: P2 M Global Theory Sharp Gradient sharp At sum  57325bd9992d
-- statement:
--   The P2 M Global Theory Sharp Gradient sharp At sum  57325bd9992d construction uses the P2 M Global Theory Sharp Gradient sharp At sum  57325bd9992d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ContinuousInvLeadingBlockEntry.lean#L83-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ContinuousInvLeadingBlockEntry.lean#L83-L89

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.SharpGradient
open Filter Matrix
open scoped ComplexOrder ComplexConjugate
variable {n : ℕ}

theorem P2M_GlobalTheory_SharpGradient_sharpAt_sum__57325bd9992d {ι : Type} [Fintype ι] {u : ι → V n → ℝ} {x : V n} {ξ : Fin n → ℂ}
    (h : ∀ i, SharpAt (u i) x ξ) : SharpAt (fun y => ∑ i, u i y) x ξ := by sorry

alias «GlobalTheory».«SharpGradient».«sharpAt_sum'» := P2M_GlobalTheory_SharpGradient_sharpAt_sum__57325bd9992d
