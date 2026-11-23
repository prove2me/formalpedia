-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Tens_prod_sum_pi
-- name    : PI.ScPiBuildW.Tens.prod_sum_pi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:27.663128+00:00
-- url     : https://prove2.me/theorems/ec7ecb9f-d2be-41eb-aa5a-b857cdbca93a
-- title:
--   Tens: prod sum pi
-- statement:
--   The Tens construction uses the prod sum pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/ContinuousOnTensOp.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/ContinuousOnTensOp.lean#L30-L32

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

theorem PI.ScPiBuildW.Tens.prod_sum_pi {κ : ι → Type} [∀ i, Fintype (κ i)] (f : ∀ i, κ i → ℂ) :
    ∏ i, ∑ j, f i j = ∑ p : (∀ i, κ i), ∏ i, f i (p i) := by sorry
