-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Tens_clm_ext
-- name    : PI.ScPiBuildW.Tens.clm_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:00:37.333849+00:00
-- url     : https://prove2.me/theorems/8562abe4-80f2-42fd-a9b1-7799e1e8cfa8
-- title:
--   Tens: clm ext
-- statement:
--   The Tens construction uses the clm ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/ContinuousOnTensOp.lean#L83-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/ContinuousOnTensOp.lean#L83-L84

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

theorem PI.ScPiBuildW.Tens.clm_ext {T T' : TV Vl →L[ℂ] TV Vl} (h : ∀ x, T (tensU x) = T' (tensU x)) : T = T' := by sorry
