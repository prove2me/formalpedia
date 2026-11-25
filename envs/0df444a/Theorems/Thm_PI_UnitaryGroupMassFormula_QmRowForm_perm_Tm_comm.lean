-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmRowForm_perm_Tm_comm
-- name    : PI.UnitaryGroupMassFormula.QmRowForm.perm_Tm_comm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:40:21.430853+00:00
-- url     : https://prove2.me/theorems/c79a0ec0-d66a-43ae-a31e-f380172252a4
-- title:
--   Qm Row Form: perm Tm comm
-- statement:
--   The Qm Row Form construction uses the perm Tm comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowFormPermutationSplit/PermutedRowProductSplit.lean#L22-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowFormPermutationSplit/PermutedRowProductSplit.lean#L22-L39

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_PermutedRowProductSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmRowForm

theorem PI.UnitaryGroupMassFormula.QmRowForm.perm_Tm_comm {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (x y : ℂ)
    (a b c d : Fin n) :
    Tm E x a b * Tm E y c d - Tm E y c d * Tm E x a b = E a b * E c d - E c d * E a b := by sorry
