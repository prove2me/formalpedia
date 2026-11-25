-- Prove2me | Theorems.Thm_P2M_PI_DatumConjInvWork_II_mul__0a00f185cfa1
-- name    : P2M_PI_DatumConjInvWork_II_mul__0a00f185cfa1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:56:17.609468+00:00
-- url     : https://prove2.me/theorems/9648ad72-d4a7-495a-8d6b-6088bc678063
-- title:
--   P2 M PI Datum Conj Inv Work II mul  0a00f185cfa1: P2 M PI Datum Conj Inv Work II mul  0a00f185cfa1
-- statement:
--   The P2 M PI Datum Conj Inv Work II mul  0a00f185cfa1 construction uses the P2 M PI Datum Conj Inv Work II mul  0a00f185cfa1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugationInvariance/SecondRowsBlockDiagMul.lean#L32-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugationInvariance/SecondRowsBlockDiagMul.lean#L32-L39

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

theorem P2M_PI_DatumConjInvWork_II_mul__0a00f185cfa1 (O : Subring F) (ϖ : F) (y : Matrix (Fin t) (Fin a) F)
    (hy : y ∈ Formalism.DoubleCosetMeasures.IIset O ϖ) (g : Matrix (Fin a) (Fin a) F) (hg : ∀ i j, g i j ∈ O) :
    y * g ∈ Formalism.DoubleCosetMeasures.IIset O ϖ := by sorry

alias «PI».«DatumConjInvWork».«II_mul'» := P2M_PI_DatumConjInvWork_II_mul__0a00f185cfa1
