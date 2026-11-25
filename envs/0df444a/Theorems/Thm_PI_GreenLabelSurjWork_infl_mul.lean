-- Prove2me | Theorems.Thm_PI_GreenLabelSurjWork_infl_mul
-- name    : PI.GreenLabelSurjWork.infl_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:30:57.053689+00:00
-- url     : https://prove2.me/theorems/a262cd8a-e48d-46a4-a7b6-fee790955c49
-- title:
--   Green Label Surj Work: infl mul
-- statement:
--   The Green Label Surj Work construction uses the infl mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelSurjective/ExistsNeZeroTensor.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelSurjective/ExistsNeZeroTensor.lean#L25-L32

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_ExistsNeZeroTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
open PI PI.GreenLabelSurjWork
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)
  (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))

theorem PI.GreenLabelSurjWork.infl_mul (p q : parab K b) :
    infl K b lam (p * q) = infl K b lam p ∘ₗ infl K b lam q := by sorry
