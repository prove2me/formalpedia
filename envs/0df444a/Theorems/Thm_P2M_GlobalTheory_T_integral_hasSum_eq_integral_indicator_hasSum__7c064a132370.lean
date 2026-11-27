-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_integral_hasSum_eq_integral_indicator_hasSum__7c064a132370
-- name    : P2M_GlobalTheory_T_integral_hasSum_eq_integral_indicator_hasSum__7c064a132370
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:48:04.602085+00:00
-- url     : https://prove2.me/theorems/96b28f37-4fa7-40f5-ab5c-f6d86d5e11d3
-- title:
--   P2 M Global Theory T integral has Sum eq integral indicator has Sum  7c064a132370: P2 M Global Theory T integral has Sum eq integral indicator has Sum  7c064a132370
-- statement:
--   The P2 M Global Theory T integral has Sum eq integral indicator has Sum  7c064a132370 construction uses the P2 M Global Theory T integral has Sum eq integral indicator has Sum  7c064a132370 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralHasSumEqIntegralIndicatorHasSumStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralHasSumEqIntegralIndicatorHasSumStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralHasSumEqIntegralIndicatorHasSum
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralHasSumEqIntegralIndicatorHasSumStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_integral_hasSum_eq_integral_indicator_hasSum__7c064a132370 : ∀ {X ι : Type} [MeasurableSpace X] [Countable ι] (μ : Measure X) (k : ι → X → ℂ), (∀ i, Integrable (k i) μ) → {i | ∫ x, ‖k i x‖ ∂μ ≠ 0}.Finite → ∀ (p : Set ι) (K Kp : X → ℂ), (∀ x, HasSum (fun i => k i x) (K x)) → (∀ x, HasSum (fun i => p.indicator (fun i => k i x) i) (Kp x)) → (∀ i ∉ p, ∫ x, k i x ∂μ = 0) → ∫ x, K x ∂μ = ∫ x, Kp x ∂μ := by sorry

alias «GlobalTheory».«T».«integral_hasSum_eq_integral_indicator_hasSum'» := P2M_GlobalTheory_T_integral_hasSum_eq_integral_indicator_hasSum__7c064a132370
