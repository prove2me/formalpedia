-- Prove2me | Theorems.Thm_PI_OpWords_rop_mul
-- name    : PI.OpWords.rop_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:35:33.662126+00:00
-- url     : https://prove2.me/theorems/1605b329-bb7b-5f3a-b4d4-1783be44340a
-- title:
--   Op Words: rop mul
-- statement:
--   The Op Words construction uses the rop mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/VanishExp.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/VanishExp.lean#L20-L24

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

theorem PI.OpWords.rop_mul (a b : Fin k) (f g : Pol K k) :
    Rop K k a b (f * g) = Rop K k a b f * g + f * Rop K k a b g := by sorry
