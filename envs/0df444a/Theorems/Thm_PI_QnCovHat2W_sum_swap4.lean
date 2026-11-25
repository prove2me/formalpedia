-- Prove2me | Theorems.Thm_PI_QnCovHat2W_sum_swap4
-- name    : PI.QnCovHat2W.sum_swap4
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:04:43.182316+00:00
-- url     : https://prove2.me/theorems/2211b2fa-0b77-5cae-a365-8e573488cbad
-- title:
--   Qn Cov Hat2 W: sum swap4
-- statement:
--   The Qn Cov Hat2 W construction uses the sum swap4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SumSgnLProdCol.lean#L59-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SumSgnLProdCol.lean#L59-L67

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

theorem PI.QnCovHat2W.sum_swap4 {ι κ : Type*} [Fintype ι] [Fintype κ] {M : Type*} [AddCommMonoid M]
    (f : ι → ι → κ → κ → M) :
    ∑ c, ∑ d, ∑ x, ∑ y, f c d x y = ∑ x, ∑ y, ∑ c, ∑ d, f c d x y := by sorry
