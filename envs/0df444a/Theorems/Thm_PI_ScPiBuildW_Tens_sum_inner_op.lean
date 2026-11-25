-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Tens_sum_inner_op
-- name    : PI.ScPiBuildW.Tens.sum_inner_op
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:21:55.87187+00:00
-- url     : https://prove2.me/theorems/eda956c5-e9f9-4ee3-a3af-74f1ab73fe19
-- title:
--   Tens: sum inner op
-- statement:
--   The Tens construction uses the sum inner op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/ContinuousOnTensOp.lean#L97-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/ContinuousOnTensOp.lean#L97-L103

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

theorem PI.ScPiBuildW.Tens.sum_inner_op {V' : Type} [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (A : V' →L[ℂ] V')
    {m : Type} [Fintype m] (b : OrthonormalBasis m ℂ V') (u x : V') :
    ∑ j, ⟪u, A (b j)⟫_ℂ * ⟪b j, x⟫_ℂ = ⟪u, A x⟫_ℂ := by sorry
