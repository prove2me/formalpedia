-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Tens_tensOp_apply
-- name    : PI.ScPiBuildW.Tens.tensOp_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:40.883603+00:00
-- url     : https://prove2.me/theorems/985dbba4-4c0b-4f5b-b898-7b0046c93f2e
-- title:
--   Tens: tens Op apply
-- statement:
--   The Tens construction uses the tens Op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/ContinuousOnTensOp.lean#L92-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/ContinuousOnTensOp.lean#L92-L95

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

theorem PI.ScPiBuildW.Tens.tensOp_apply (A : ∀ i, Vl i →L[ℂ] Vl i) (v : TV Vl) (p : Idx Vl) :
    tensOp A v p = ∑ q, opMat A p q * v q := by sorry
