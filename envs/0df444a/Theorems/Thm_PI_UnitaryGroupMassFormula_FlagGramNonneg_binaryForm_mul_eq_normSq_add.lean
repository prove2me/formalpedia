-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_binaryForm_mul_eq_normSq_add
-- name    : PI.UnitaryGroupMassFormula.FlagGramNonneg.binaryForm_mul_eq_normSq_add
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:38:45.406261+00:00
-- url     : https://prove2.me/theorems/f51c76be-51d4-4dd7-abd4-84c08d580e01
-- title:
--   Flag Gram Nonneg: binary Form mul eq norm Sq add
-- statement:
--   The Flag Gram Nonneg construction uses the binary Form mul eq norm Sq add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/BinaryFormMulEqNormSqAdd.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/BinaryFormMulEqNormSqAdd.lean#L12-L17

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_BinaryFormMulEqNormSqAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FlagGramNonneg

theorem PI.UnitaryGroupMassFormula.FlagGramNonneg.binaryForm_mul_eq_normSq_add (T T' : ℝ) (s x y : ℂ) :
    T * (T * Complex.normSq x + T' * Complex.normSq y - 2 * (conj x * s * y).re) =
      Complex.normSq ((T : ℂ) * x - s * y) + (T * T' - Complex.normSq s) * Complex.normSq y := by sorry
