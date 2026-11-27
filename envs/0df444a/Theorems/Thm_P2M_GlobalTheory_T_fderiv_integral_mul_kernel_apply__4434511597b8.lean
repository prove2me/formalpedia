-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_fderiv_integral_mul_kernel_apply__4434511597b8
-- name    : P2M_GlobalTheory_T_fderiv_integral_mul_kernel_apply__4434511597b8
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:06:58.847915+00:00
-- url     : https://prove2.me/theorems/5622ddc5-2593-4be0-9b1c-e38874cfcd26
-- title:
--   P2 M Global Theory T fderiv integral mul kernel apply  4434511597b8: P2 M Global Theory T fderiv integral mul kernel apply  4434511597b8
-- statement:
--   The P2 M Global Theory T fderiv integral mul kernel apply  4434511597b8 construction uses the P2 M Global Theory T fderiv integral mul kernel apply  4434511597b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FderivIntegralMulKernelApplyStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FderivIntegralMulKernelApplyStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FderivIntegralMulKernelApply
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FderivIntegralMulKernelApplyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Metric
open scoped ContDiff
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_fderiv_integral_mul_kernel_apply__4434511597b8 : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (ν : Measure V) [ν.IsAddHaarMeasure] {U : Set V}, IsOpen U → ∀ {α : V → ℂ}, Continuous α → HasCompactSupport α → tsupport α ⊆ U → ∀ {K : V × V → ℂ}, ContDiffOn ℝ ∞ K (U ×ˢ U) → ∀ {x : V}, x ∈ U → ∀ v : V, fderiv ℝ (fun x' => ∫ y, α y * K (x', y) ∂ν) x v = ∫ y, α y * fderiv ℝ (fun x' => K (x', y)) x v ∂ν := by sorry

alias «GlobalTheory».«T».«fderiv_integral_mul_kernel_apply'» := P2M_GlobalTheory_T_fderiv_integral_mul_kernel_apply__4434511597b8
