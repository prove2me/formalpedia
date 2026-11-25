-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmRowForm_Tm_opE
-- name    : PI.UnitaryGroupMassFormula.QmRowForm.Tm_opE
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:39:48.40881+00:00
-- url     : https://prove2.me/theorems/92f04974-675c-46e0-8f7d-e9b31ad1fdd7
-- title:
--   Qm Row Form: Tm op E
-- statement:
--   The Qm Row Form construction uses the Tm op E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowFormPermutationSplit/DoubleRowIncreasing.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowFormPermutationSplit/DoubleRowIncreasing.lean#L22-L28

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_DoubleRowIncreasing
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

theorem PI.UnitaryGroupMassFormula.QmRowForm.Tm_opE {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (x : ℂ) (a b : Fin n) :
    Tm (opE E) x a b = MulOpposite.op (Tm E x b a) := by sorry
