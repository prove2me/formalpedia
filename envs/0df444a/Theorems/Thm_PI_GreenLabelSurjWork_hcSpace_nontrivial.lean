-- Prove2me | Theorems.Thm_PI_GreenLabelSurjWork_hcSpace_nontrivial
-- name    : PI.GreenLabelSurjWork.hcSpace_nontrivial
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:31:15.300539+00:00
-- url     : https://prove2.me/theorems/030dc3ef-f4f3-43f3-bf87-6f729206de77
-- title:
--   Green Label Surj Work: hc Space nontrivial
-- statement:
--   The Green Label Surj Work construction uses the hc Space nontrivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelSurjective/ExistsNeZeroTensor.lean#L53-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelSurjective/ExistsNeZeroTensor.lean#L53-L74

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

theorem PI.GreenLabelSurjWork.hcSpace_nontrivial (hl : ∀ c, Nontrivial (lam c)) : Nontrivial (hcSpace K b lam) := by sorry
