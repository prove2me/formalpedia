-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Tens_tensOp_mul
-- name    : PI.ScPiBuildW.Tens.tensOp_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:21:53.424329+00:00
-- url     : https://prove2.me/theorems/c6f0bb6e-2718-55b2-99e9-e4ef16c77aa5
-- title:
--   Tens: tens Op mul
-- statement:
--   The Tens construction uses the tens Op mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/ContinuousOnTensOp.lean#L117-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/ContinuousOnTensOp.lean#L117-L121

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

theorem PI.ScPiBuildW.Tens.tensOp_mul (A B : ∀ i, Vl i →L[ℂ] Vl i) :
    tensOp (fun i => A i * B i) = tensOp A * tensOp B := by sorry
