-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmRowForm_perm_swap
-- name    : PI.UnitaryGroupMassFormula.QmRowForm.perm_swap
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:40:44.621793+00:00
-- url     : https://prove2.me/theorems/1ebe0b7c-9e0e-4733-a0f3-383c4eb269fe
-- title:
--   Qm Row Form: perm swap
-- statement:
--   The Qm Row Form construction uses the perm swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowFormPermutationSplit/PermutedRowProductSplit.lean#L104-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowFormPermutationSplit/PermutedRowProductSplit.lean#L104-L172

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

theorem PI.UnitaryGroupMassFormula.QmRowForm.perm_swap {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (a b : Fin (m + 1) → Fin n) (x : Fin (m + 1) → ℂ) (i : Fin m) :
    doubleRowFormSum E a b (x ∘ Equiv.swap i.castSucc i.succ) = doubleRowFormSum E a b x := by sorry
