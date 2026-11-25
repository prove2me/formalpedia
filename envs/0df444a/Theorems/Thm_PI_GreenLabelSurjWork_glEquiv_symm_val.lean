-- Prove2me | Theorems.Thm_PI_GreenLabelSurjWork_glEquiv_symm_val
-- name    : PI.GreenLabelSurjWork.glEquiv_symm_val
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:30:54.704713+00:00
-- url     : https://prove2.me/theorems/bc97f976-a683-4d7b-92c3-0d8a8fabac52
-- title:
--   Green Label Surj Work: gl Equiv symm val
-- statement:
--   The Green Label Surj Work construction uses the gl Equiv symm val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelSurjective/Transp.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelSurjective/Transp.lean#L15-L16

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
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
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem PI.GreenLabelSurjWork.glEquiv_symm_val (e : ι ≃ κ) (g : GL κ K) :
    (((glEquiv K e).symm g : GL ι K) : Matrix ι ι K) = Matrix.reindex e.symm e.symm (g : Matrix κ κ K) := by sorry
