-- Prove2me | Theorems.Thm_PI_PolynomialProperness_TauN_nEich_heis
-- name    : PI.PolynomialProperness.TauN.nEich_heis
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:47:46.670062+00:00
-- url     : https://prove2.me/theorems/35840071-8c86-5b8b-91ff-c74d45e717c2
-- title:
--   Tau N: n Eich heis
-- statement:
--   The Tau N construction uses the n Eich heis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermitianXiOrthogonal.lean#L84-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermitianXiOrthogonal.lean#L84-L95

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

theorem PI.PolynomialProperness.TauN.nEich_heis {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : StdZ k r z) (ξ : Fin r → ℂ)
    (u : Fin (2 * r + k + 1) → ℂ) :
    nEich k r z ξ *ᵥ u = u - herm (Hpk k r) u (((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) • z) • xiV k r ξ +
      herm (Hpk k r) u (xiV k r ξ) • (((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) • z +
        ((1 : ℂ) / (2 * ((Tz k r z : ℝ) : ℂ))) • xiV k r ξ) := by sorry
