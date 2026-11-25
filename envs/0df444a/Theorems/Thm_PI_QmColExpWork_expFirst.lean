-- Prove2me | Theorems.Thm_PI_QmColExpWork_expFirst
-- name    : PI.QmColExpWork.expFirst
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:20:15.335189+00:00
-- url     : https://prove2.me/theorems/aaa477cb-bef7-5a49-938d-cd8d94c9525b
-- title:
--   Qm Col Exp Work: exp First
-- statement:
--   The Qm Col Exp Work construction uses the exp First property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialFirstColumn/FirstColumnSplitBijective.lean#L67-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialFirstColumn/FirstColumnSplitBijective.lean#L67-L95

import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialFirstColumn_FirstColumnSplitBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.QmColExpWork
open Formalism.REAL

theorem PI.QmColExpWork.expFirst {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin (m + 1) → Fin n) (u : ℂ) :
    qminor E a b u = ∑ j : Fin (m + 1), (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) *
      (Tm E u (a j) (b 0) * qminor E (a ∘ j.succAbove) (b ∘ Fin.succ) (u - 1)) := by sorry
