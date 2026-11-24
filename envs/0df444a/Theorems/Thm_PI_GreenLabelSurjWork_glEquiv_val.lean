-- Prove2me | Theorems.Thm_PI_GreenLabelSurjWork_glEquiv_val
-- name    : PI.GreenLabelSurjWork.glEquiv_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:04.140851+00:00
-- url     : https://prove2.me/theorems/93a59272-6d7c-40ca-ba4d-d02be2fa74fe
-- title:
--   Green Label Surj Work: gl Equiv val
-- statement:
--   The Green Label Surj Work construction uses the gl Equiv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelSurjective/Transp.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelSurjective/Transp.lean#L12-L13

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

theorem PI.GreenLabelSurjWork.glEquiv_val (e : ι ≃ κ) (g : GL ι K) :
    ((glEquiv K e g : GL κ K) : Matrix κ κ K) = Matrix.reindex e e (g : Matrix ι ι K) := by sorry
