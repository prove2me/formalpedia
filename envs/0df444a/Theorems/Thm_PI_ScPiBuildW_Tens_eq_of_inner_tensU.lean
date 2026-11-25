-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Tens_eq_of_inner_tensU
-- name    : PI.ScPiBuildW.Tens.eq_of_inner_tensU
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:21:47.76572+00:00
-- url     : https://prove2.me/theorems/92209aba-ff17-4e14-9a72-57c8f70eda27
-- title:
--   Tens: eq of inner tens U
-- statement:
--   The Tens construction uses the eq of inner tens U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/ContinuousOnTensOp.lean#L72-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/ContinuousOnTensOp.lean#L72-L81

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

theorem PI.ScPiBuildW.Tens.eq_of_inner_tensU {v v' : TV Vl} (h : ∀ x, ⟪tensU x, v⟫_ℂ = ⟪tensU x, v'⟫_ℂ) : v = v' := by sorry
