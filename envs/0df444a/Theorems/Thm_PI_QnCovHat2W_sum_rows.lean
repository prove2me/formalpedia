-- Prove2me | Theorems.Thm_PI_QnCovHat2W_sum_rows
-- name    : PI.QnCovHat2W.sum_rows
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:38:18.823354+00:00
-- url     : https://prove2.me/theorems/da23189b-a1de-4136-9b3e-15668fcdf065
-- title:
--   Qn Cov Hat2 W: sum rows
-- statement:
--   The Qn Cov Hat2 W construction uses the sum rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SumSgnLProdCol.lean#L9-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SumSgnLProdCol.lean#L9-L25

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_GGEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SumSgnLProdCol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnCovHat2W
open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem PI.QnCovHat2W.sum_rows {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommGroup M]
    [Module ℂ M] (p : Fin (m + 2) → α → ℂ) (f g : α → ℂ) (Φ : (Fin m → α) → M) :
    ∑ x : Fin (m + 2) → α, (f (x 0) * g (x 1) * ∏ k, p k (x k)) • Φ (fun k => x k.succ.succ) =
      ((∑ z, f z * p 0 z) * (∑ z, g z * p 1 z)) •
        ∑ y : Fin m → α, (∏ k, p k.succ.succ (y k)) • Φ y := by sorry
