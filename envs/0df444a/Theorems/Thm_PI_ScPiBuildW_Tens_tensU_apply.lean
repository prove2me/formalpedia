-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Tens_tensU_apply
-- name    : PI.ScPiBuildW.Tens.tensU_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:00:47.980807+00:00
-- url     : https://prove2.me/theorems/f4b5b707-231e-4bb3-924b-7885e9d7eb4f
-- title:
--   Tens: tens U apply
-- statement:
--   The Tens construction uses the tens U apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/ContinuousOnTensOp.lean#L28-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/ContinuousOnTensOp.lean#L28-L28

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

theorem PI.ScPiBuildW.Tens.tensU_apply (x : ∀ i, Vl i) (p : Idx Vl) : tensU x p = ∏ i, ⟪bas Vl i (p i), x i⟫_ℂ := by sorry
