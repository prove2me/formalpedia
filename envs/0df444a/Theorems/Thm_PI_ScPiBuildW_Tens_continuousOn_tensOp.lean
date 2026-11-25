-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Tens_continuousOn_tensOp
-- name    : PI.ScPiBuildW.Tens.continuousOn_tensOp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:21:36.249921+00:00
-- url     : https://prove2.me/theorems/805256d3-14a6-4178-ab85-30f9d9140c6c
-- title:
--   Tens: continuous On tens Op
-- statement:
--   The Tens construction uses the continuous On tens Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/ContinuousOnTensOp.lean#L133-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/ContinuousOnTensOp.lean#L133-L149

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

theorem PI.ScPiBuildW.Tens.continuousOn_tensOp {X : Type*} [TopologicalSpace X] (A : X → ∀ i, Vl i →L[ℂ] Vl i) (S : Set X)
    (hA : ∀ i (y : Vl i), ContinuousOn (fun s => A s i y) S) (v : TV Vl) :
    ContinuousOn (fun s => tensOp (A s) v) S := by sorry
