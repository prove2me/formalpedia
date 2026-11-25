-- Prove2me | Theorems.Thm_PI_PolynomialProperness_TauN_herm_xi_zero
-- name    : PI.PolynomialProperness.TauN.herm_xi_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:17:52.297257+00:00
-- url     : https://prove2.me/theorems/082a8b64-774e-5f1c-8340-99d39885c2a1
-- title:
--   Tau N: herm xi zero
-- statement:
--   The Tau N construction uses the herm xi zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermitianXiOrthogonal.lean#L39-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermitianXiOrthogonal.lean#L39-L59

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermitianXiOrthogonal
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
open PI PI.PolynomialProperness PI.PolynomialProperness.TauN

theorem PI.PolynomialProperness.TauN.herm_xi_zero (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ)
    (hy : ∀ i : Fin (2 * r + k + 1), r + k < i.val → y i = 0) (p : Fin r → ℂ) :
    herm (Hpk k r) y (xiV k r p) = 0 := by sorry
