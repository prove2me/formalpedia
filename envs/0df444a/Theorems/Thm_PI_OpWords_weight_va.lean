-- Prove2me | Theorems.Thm_PI_OpWords_weight_va
-- name    : PI.OpWords.weight_va
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:16:57.361802+00:00
-- url     : https://prove2.me/theorems/ddc6a992-a01b-5e80-867a-0a29c9f2546f
-- title:
--   Op Words: weight va
-- statement:
--   The Op Words construction uses the weight va property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/PolarizationBihomogeneous.lean#L99-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/PolarizationBihomogeneous.lean#L99-L101

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

theorem PI.OpWords.weight_va (k : ℕ) (a : Fin k) (m : Fin k ⊕ Fin k →₀ ℕ) :
    weight (va k a) m = (m (Sum.inl a) : ℤ) - m (Sum.inr a) := by sorry
