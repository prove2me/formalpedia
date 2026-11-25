-- Prove2me | Theorems.Thm_PI_DatumConjInvWork_firstRows_mul
-- name    : PI.DatumConjInvWork.firstRows_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:26:29.703517+00:00
-- url     : https://prove2.me/theorems/4562d8b6-dc94-5075-be62-0e2e601ffaa4
-- title:
--   Datum Conj Inv Work: first Rows mul
-- statement:
--   The Datum Conj Inv Work construction uses the first Rows mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugationInvariance/SecondRowsBlockDiagMul.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugationInvariance/SecondRowsBlockDiagMul.lean#L12-L15

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DatumConjInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugationInvariance_SecondRowsBlockDiagMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.DatumConjInvWork
variable {F : Type} [Field F] {a t : ℕ}

theorem PI.DatumConjInvWork.firstRows_mul (x : Matrix (Fin a ⊕ Fin t) (Fin a) F) (g : Matrix (Fin a) (Fin a) F) :
    toRows₁ (x * g) = toRows₁ x * g := by sorry
