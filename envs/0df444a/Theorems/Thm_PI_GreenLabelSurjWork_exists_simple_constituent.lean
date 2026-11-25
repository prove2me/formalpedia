-- Prove2me | Theorems.Thm_PI_GreenLabelSurjWork_exists_simple_constituent
-- name    : PI.GreenLabelSurjWork.exists_simple_constituent
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:30:59.594366+00:00
-- url     : https://prove2.me/theorems/0ddea35d-eebc-4b5f-90f8-0b2d68f10edc
-- title:
--   Green Label Surj Work: exists simple constituent
-- statement:
--   The Green Label Surj Work construction uses the exists simple constituent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelSurjective/Simple.lean#L29-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelSurjective/Simple.lean#L29-L72

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Simple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
open PI PI.GreenLabelSurjWork
variable {G : Type} [Group G] [Fintype G]

theorem PI.GreenLabelSurjWork.exists_simple_constituent {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [Nontrivial V] (ρ : Representation ℂ G V) : ∃ τ : FDRep ℂ G, Simple τ ∧ IsConstituent τ ρ := by sorry
