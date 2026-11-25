-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_gamma_neg
-- name    : PI.UnitaryGroupMassFormula.FlagGramNonneg.gamma_neg
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:39:12.081185+00:00
-- url     : https://prove2.me/theorems/a1ce675a-2614-4593-a596-d207e989585c
-- title:
--   Flag Gram Nonneg: gamma neg
-- statement:
--   The Flag Gram Nonneg construction uses the gamma neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/BinaryFormMulEqNormSqAdd.lean#L68-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/BinaryFormMulEqNormSqAdd.lean#L68-L115

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

theorem PI.UnitaryGroupMassFormula.FlagGramNonneg.gamma_neg (r : ℕ) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (s : ℂ)
    (hs : Complex.normSq s < T * T') (c : Fin r ⊕ Fin 2 → ℂ) (hc : c ≠ 0) :
    (star c ⬝ᵥ (gamma r T T' s *ᵥ c)).re < 0 := by sorry
