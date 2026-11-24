-- Prove2me | Theorems.Thm_PI_PolynomialProperness_TauN_nEich_mulVec
-- name    : PI.PolynomialProperness.TauN.nEich_mulVec
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:51:52.193169+00:00
-- url     : https://prove2.me/theorems/78aa56cb-4a21-4e7f-9057-abf53d1cd1a5
-- title:
--   Tau N: n Eich mul Vec
-- statement:
--   The Tau N construction uses the n Eich mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermitianXiOrthogonal.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermitianXiOrthogonal.lean#L31-L37

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

theorem PI.PolynomialProperness.TauN.nEich_mulVec (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (ξ : Fin r → ℂ)
    (u : Fin (2 * r + k + 1) → ℂ) :
    nEich k r z ξ *ᵥ u = u + ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) •
      (-(herm (Hpk k r) u z • xiV k r ξ) + herm (Hpk k r) u (xiV k r ξ) • z +
        ((1 / 2 : ℂ) * herm (Hpk k r) u (xiV k r ξ)) • xiV k r ξ) := by sorry
