-- Prove2me | Theorems.Thm_PI_OpWords_tt_va
-- name    : PI.OpWords.tt_va
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:16:45.319085+00:00
-- url     : https://prove2.me/theorems/de2994bb-214f-507d-aa04-23f7f6314912
-- title:
--   Op Words: tt va
-- statement:
--   The Op Words construction uses the tt va property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/PolarizationBihomogeneous.lean#L103-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/PolarizationBihomogeneous.lean#L103-L110

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PolarizationBihomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finsupp
noncomputable section
open PI PI.OpWords

theorem PI.OpWords.tt_va (K : Type) [Field K] (k : ℕ) (a : Fin k) :
    IsWeightedHomogeneous (va k a) (tt K k) 0 := by sorry
