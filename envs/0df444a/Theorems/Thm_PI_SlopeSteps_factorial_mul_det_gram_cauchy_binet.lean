-- Prove2me | Theorems.Thm_PI_SlopeSteps_factorial_mul_det_gram_cauchy_binet
-- name    : PI.SlopeSteps.factorial_mul_det_gram_cauchy_binet
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:01:35.890513+00:00
-- url     : https://prove2.me/theorems/c24cb064-34ad-41d9-8b85-3e44e976dc0d
-- title:
--   Slope Steps: factorial mul det gram cauchy binet
-- statement:
--   The Slope Steps construction uses the factorial mul det gram cauchy binet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StandardSlopeBound/NablaGram.lean#L26-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StandardSlopeBound/NablaGram.lean#L26-L54

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_MonomialFactorizationLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_StdSlopeLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_GramMatrixDuality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SlopeSteps
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV Matrix

theorem PI.SlopeSteps.factorial_mul_det_gram_cauchy_binet {R : Type*} [CommRing R] (k : ℕ) {n : Type*} [Fintype n] [DecidableEq n]
    (q : n → R) (V : Matrix n (Fin k) R) :
    (k.factorial : R) * (Vᵀ * diagonal q * V).det =
      ∑ f : Fin k → n, (∏ i, q (f i)) * ((V.submatrix f id).det * (Vᵀ.submatrix id f).det) := by sorry
