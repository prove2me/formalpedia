-- Prove2me | Theorems.Thm_PI_QnCovHat2W_sum_sgnL_prod_col
-- name    : PI.QnCovHat2W.sum_sgnL_prod_col
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:38:08.120268+00:00
-- url     : https://prove2.me/theorems/073b751f-126e-4f43-a7fc-bac403292541
-- title:
--   Qn Cov Hat2 W: sum sgn L prod col
-- statement:
--   The Qn Cov Hat2 W construction uses the sum sgn L prod col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SumSgnLProdCol.lean#L43-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SumSgnLProdCol.lean#L43-L57

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

theorem PI.QnCovHat2W.sum_sgnL_prod_col {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℂ) (y : Fin N → Fin N) :
    ∑ d : Fin N → Fin N, sgnL d id * ∏ k, Q (d k) (y k) = sgnL y id * Q.det := by sorry
