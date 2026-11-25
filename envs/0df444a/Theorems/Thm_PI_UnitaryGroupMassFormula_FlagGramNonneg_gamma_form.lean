-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_gamma_form
-- name    : PI.UnitaryGroupMassFormula.FlagGramNonneg.gamma_form
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:38:42.670025+00:00
-- url     : https://prove2.me/theorems/ac55f4c8-688a-5371-a0e7-ea654701b3db
-- title:
--   Flag Gram Nonneg: gamma form
-- statement:
--   The Flag Gram Nonneg construction uses the gamma form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/BinaryFormMulEqNormSqAdd.lean#L24-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/BinaryFormMulEqNormSqAdd.lean#L24-L66

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

theorem PI.UnitaryGroupMassFormula.FlagGramNonneg.gamma_form (r : ℕ) (T T' : ℝ) (s : ℂ) (c : Fin r ⊕ Fin 2 → ℂ) :
    (star c ⬝ᵥ (gamma r T T' s *ᵥ c)).re =
      -2 * ∑ a, Complex.normSq (c (Sum.inl a)) -
        (T * Complex.normSq (c (Sum.inr 0)) + T' * Complex.normSq (c (Sum.inr 1)) -
          2 * (conj (c (Sum.inr 0)) * s * c (Sum.inr 1)).re) := by sorry
