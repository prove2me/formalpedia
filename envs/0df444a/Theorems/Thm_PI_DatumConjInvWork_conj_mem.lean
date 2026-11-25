-- Prove2me | Theorems.Thm_PI_DatumConjInvWork_conj_mem
-- name    : PI.DatumConjInvWork.conj_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:26:23.142604+00:00
-- url     : https://prove2.me/theorems/2991743e-16a5-5417-b66e-d0f7114f4e5e
-- title:
--   Datum Conj Inv Work: conj mem
-- statement:
--   The Datum Conj Inv Work construction uses the conj mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugationInvariance/SecondRowsBlockDiagMul.lean#L59-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugationInvariance/SecondRowsBlockDiagMul.lean#L59-L77

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

theorem PI.DatumConjInvWork.conj_mem (O : Subring F) (ϖ : F) (h : GL (Fin a) F) (hh : h ∈ Formalism.DoubleCosetMeasures.GLint O a)
    (g : GL (Fin a) F) (hg : g ∈ Formalism.DoubleCosetMeasures.congSub O ϖ a) :
    h⁻¹ * g * h ∈ Formalism.DoubleCosetMeasures.congSub O ϖ a := by sorry
