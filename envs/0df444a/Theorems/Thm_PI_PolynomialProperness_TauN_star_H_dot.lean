-- Prove2me | Theorems.Thm_PI_PolynomialProperness_TauN_star_H_dot
-- name    : PI.PolynomialProperness.TauN.star_H_dot
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:19:25.016813+00:00
-- url     : https://prove2.me/theorems/a1b93a85-afa6-5c47-84ef-8f0f746ff5f5
-- title:
--   Tau N: star H dot
-- statement:
--   The Tau N construction uses the star H dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermitianXiOrthogonal.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermitianXiOrthogonal.lean#L26-L29

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

theorem PI.PolynomialProperness.TauN.star_H_dot (k r : ℕ) (w u : Fin (2 * r + k + 1) → ℂ) :
    star (Hpk k r *ᵥ w) ⬝ᵥ u = herm (Hpk k r) u w := by sorry
