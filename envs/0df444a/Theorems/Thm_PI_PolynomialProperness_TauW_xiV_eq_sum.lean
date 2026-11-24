-- Prove2me | Theorems.Thm_PI_PolynomialProperness_TauW_xiV_eq_sum
-- name    : PI.PolynomialProperness.TauW.xiV_eq_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:52:41.272608+00:00
-- url     : https://prove2.me/theorems/1468fa28-d0f9-473b-8995-6db549bdbd36
-- title:
--   Tau W: xi V eq sum
-- statement:
--   The Tau W construction uses the xi V eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/FvecCastSucc.lean#L11-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/FvecCastSucc.lean#L11-L37

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_FvecCastSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.TauW

theorem PI.PolynomialProperness.TauW.xiV_eq_sum (k r : ℕ) (p : Fin r → ℂ) : xiV k r p = ∑ a, p a • bvec (eI k r a) := by sorry
