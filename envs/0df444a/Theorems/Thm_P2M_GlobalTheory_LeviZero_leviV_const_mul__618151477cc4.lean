-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LeviZero_leviV_const_mul__618151477cc4
-- name    : P2M_GlobalTheory_LeviZero_leviV_const_mul__618151477cc4
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:37:36.031162+00:00
-- url     : https://prove2.me/theorems/3245591f-918e-458e-90ba-294ce512815d
-- title:
--   P2 M Global Theory Levi Zero levi V const mul  618151477cc4: P2 M Global Theory Levi Zero levi V const mul  618151477cc4
-- statement:
--   The P2 M Global Theory Levi Zero levi V const mul  618151477cc4 construction uses the P2 M Global Theory Levi Zero levi V const mul  618151477cc4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LeviFormWeightMetricOrthonormalDiagonal.lean#L278-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LeviFormWeightMetricOrthonormalDiagonal.lean#L278-L281

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeviFormWeightMetricOrthonormalDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.LeviZero
open Filter
open scoped ComplexConjugate
noncomputable section
variable {n : ℕ} {ξ : Fin n → ℂ} {x : V n}

theorem P2M_GlobalTheory_LeviZero_leviV_const_mul__618151477cc4 (c : ℂ) {f : V n → ℂ} (h : ContDiffAt ℝ 2 f x) :
    leviV n (fun y => c * f y) x ξ = c * leviV n f x ξ := by sorry

alias «GlobalTheory».«LeviZero».«leviV_const_mul'» := P2M_GlobalTheory_LeviZero_leviV_const_mul__618151477cc4
