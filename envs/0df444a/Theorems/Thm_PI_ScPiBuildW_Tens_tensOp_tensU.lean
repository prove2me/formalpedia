-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Tens_tensOp_tensU
-- name    : PI.ScPiBuildW.Tens.tensOp_tensU
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:01:00.431816+00:00
-- url     : https://prove2.me/theorems/9c6f0ae0-670e-4764-a5af-0e5866fed3da
-- title:
--   Tens: tens Op tens U
-- statement:
--   The Tens construction uses the tens Op tens U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/ContinuousOnTensOp.lean#L105-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/ContinuousOnTensOp.lean#L105-L112

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

theorem PI.ScPiBuildW.Tens.tensOp_tensU (A : ∀ i, Vl i →L[ℂ] Vl i) (x : ∀ i, Vl i) :
    tensOp A (tensU x) = tensU (fun i => A i (x i)) := by sorry
