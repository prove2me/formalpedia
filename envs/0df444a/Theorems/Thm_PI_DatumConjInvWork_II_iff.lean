-- Prove2me | Theorems.Thm_PI_DatumConjInvWork_II_iff
-- name    : PI.DatumConjInvWork.II_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:26:49.044282+00:00
-- url     : https://prove2.me/theorems/cae02ccb-1780-421c-830c-2cd46765f046
-- title:
--   Datum Conj Inv Work: II iff
-- statement:
--   The Datum Conj Inv Work construction uses the II iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugationInvariance/SecondRowsBlockDiagMul.lean#L41-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugationInvariance/SecondRowsBlockDiagMul.lean#L41-L51

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

theorem PI.DatumConjInvWork.II_iff (O : Subring F) (ϖ : F) (k : GL (Fin a) F) (hk : k ∈ Formalism.DoubleCosetMeasures.GLint O a)
    (y : Matrix (Fin t) (Fin a) F) :
    y * (k : Matrix (Fin a) (Fin a) F) ∈ Formalism.DoubleCosetMeasures.IIset O ϖ ↔ y ∈ Formalism.DoubleCosetMeasures.IIset O ϖ := by sorry
