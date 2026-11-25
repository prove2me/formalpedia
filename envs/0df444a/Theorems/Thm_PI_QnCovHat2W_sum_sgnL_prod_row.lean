-- Prove2me | Theorems.Thm_PI_QnCovHat2W_sum_sgnL_prod_row
-- name    : PI.QnCovHat2W.sum_sgnL_prod_row
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:38:46.55779+00:00
-- url     : https://prove2.me/theorems/f07caa9a-ae39-4a85-b383-723572d6617a
-- title:
--   Qn Cov Hat2 W: sum sgn L prod row
-- statement:
--   The Qn Cov Hat2 W construction uses the sum sgn L prod row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SumSgnLProdCol.lean#L27-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SumSgnLProdCol.lean#L27-L41

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

theorem PI.QnCovHat2W.sum_sgnL_prod_row {N : ℕ} (P : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → Fin N) :
    ∑ c : Fin N → Fin N, sgnL c id * ∏ k, P (x k) (c k) = sgnL x id * P.det := by sorry
