-- Prove2me | Theorems.Thm_PI_OpWords_rop_iter_mul_X
-- name    : PI.OpWords.rop_iter_mul_X
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:35:42.300122+00:00
-- url     : https://prove2.me/theorems/7ac5ee1f-90d4-4a10-b2ae-a69b3768546c
-- title:
--   Op Words: rop iter mul X
-- statement:
--   The Op Words construction uses the rop iter mul X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/VanishExp.lean#L38-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/VanishExp.lean#L38-L52

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_VanishExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.OpWords
variable {K : Type} [Field K] [CharZero K] {k : ℕ}

theorem PI.OpWords.rop_iter_mul_X (a b : Fin k) (hab : a ≠ b) (g : Pol K k) (i : Fin k ⊕ Fin k) (n : ℕ) :
    (Rop K k a b)^[n + 1] (g * X i) = (Rop K k a b)^[n + 1] g * X i
      + (n + 1) • ((Rop K k a b)^[n] g * Rop K k a b (X i)) := by sorry
