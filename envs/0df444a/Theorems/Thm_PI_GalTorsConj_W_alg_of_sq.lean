-- Prove2me | Theorems.Thm_PI_GalTorsConj_W_alg_of_sq
-- name    : PI.GalTorsConj.W.alg_of_sq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:30:56.751311+00:00
-- url     : https://prove2.me/theorems/47235e9a-be1f-5821-9a25-27614d232abe
-- title:
--   W: alg of sq
-- statement:
--   The W construction uses the alg of sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/TorsValsFinite.lean#L59-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/TorsValsFinite.lean#L59-L71

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_IncAdjInclusion
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_TorsValsFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open Polynomial Formalism.L2.Th1.F

theorem PI.GalTorsConj.W.alg_of_sq {F : Type*} [Field F] [Algebra F ℂ] {x y a b : ℂ}
    (hsq : y ^ 2 = 4 * x ^ 3 - a * x - b)
    (hx : IsAlgebraic F x) (ha : IsAlgebraic F a) (hb : IsAlgebraic F b) : IsAlgebraic F y := by sorry
