-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Tens_inner_tensOp
-- name    : PI.ScPiBuildW.Tens.inner_tensOp
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:21:57.67403+00:00
-- url     : https://prove2.me/theorems/5a5b1651-4214-4c46-bdf0-c7017694b660
-- title:
--   Tens: inner tens Op
-- statement:
--   The Tens construction uses the inner tens Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/ContinuousOnTensOp.lean#L123-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/ContinuousOnTensOp.lean#L123-L131

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_ContinuousOnTensOp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ComplexConjugate
open Module
open PI PI.ScPiBuildW PI.ScPiBuildW.Tens
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Vl : ι → Type} [∀ i, NormedAddCommGroup (Vl i)] [∀ i, InnerProductSpace ℂ (Vl i)]
  [∀ i, FiniteDimensional ℂ (Vl i)]

theorem PI.ScPiBuildW.Tens.inner_tensOp (A : ∀ i, Vl i →L[ℂ] Vl i) (hA : ∀ i (u w : Vl i), ⟪A i u, A i w⟫_ℂ = ⟪u, w⟫_ℂ)
    (u w : TV Vl) : ⟪tensOp A u, tensOp A w⟫_ℂ = ⟪u, w⟫_ℂ := by sorry
