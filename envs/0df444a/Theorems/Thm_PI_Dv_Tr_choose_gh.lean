-- Prove2me | Theorems.Thm_PI_Dv_Tr_choose_gh
-- name    : PI.Dv.Tr.choose_gh
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:30:41.504651+00:00
-- url     : https://prove2.me/theorems/26f8fac7-cd96-4066-b9c4-9fc4644c771b
-- title:
--   Tr: choose gh
-- statement:
--   The Tr construction uses the choose gh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/PerSAlg.lean#L85-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/PerSAlg.lean#L85-L187

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_RankIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_PerSAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

theorem PI.Dv.Tr.choose_gh (T : GoodSet K G) (s : T.S) (P0 P : Pair K G) (hM : nS T P0 s = 1) :
    ∃ (cB : MonoidAlgebra K G → K) (g h : Fin (nS T P s) → G),
      (∀ a, eps P0 * a * eps P0 * eS T s = cB a • (eps P0 * eS T s)) ∧
      IsUnit (Matrix.of fun j i => cB (MonoidAlgebra.of K G (h j) * eps P * MonoidAlgebra.of K G (g i))) := by sorry
