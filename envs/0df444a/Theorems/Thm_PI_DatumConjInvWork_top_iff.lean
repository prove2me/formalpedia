-- Prove2me | Theorems.Thm_PI_DatumConjInvWork_top_iff
-- name    : PI.DatumConjInvWork.top_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:26:35.986425+00:00
-- url     : https://prove2.me/theorems/b4a4c76d-cc90-57fd-8a1b-5f21bd4ac76b
-- title:
--   Datum Conj Inv Work: top iff
-- statement:
--   The Datum Conj Inv Work construction uses the top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugationInvariance/SecondRowsBlockDiagMul.lean#L79-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugationInvariance/SecondRowsBlockDiagMul.lean#L79-L93

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

theorem PI.DatumConjInvWork.top_iff (O : Subring F) (ϖ : F) (k : GL (Fin a) F) (hk : k ∈ Formalism.DoubleCosetMeasures.GLint O a)
    (X : Matrix (Fin a) (Fin a) F) :
    (∃ g : Formalism.DoubleCosetMeasures.congSub O ϖ a, ((g : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) =
        ((k⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) * X * (k : Matrix (Fin a) (Fin a) F)) ↔
      (∃ g : Formalism.DoubleCosetMeasures.congSub O ϖ a, ((g : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = X) := by sorry
