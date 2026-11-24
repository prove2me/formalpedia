-- Prove2me | Theorems.Thm_P2M_PI_PolynomialProperness_TauW_fvec_last__592450600e93
-- name    : P2M_PI_PolynomialProperness_TauW_fvec_last__592450600e93
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:53:57.576152+00:00
-- url     : https://prove2.me/theorems/901b793e-6d93-410c-8206-56a6fdb4e137
-- title:
--   P2 M PI Polynomial Properness Tau W fvec last  592450600e93: P2 M PI Polynomial Properness Tau W fvec last  592450600e93
-- statement:
--   The P2 M PI Polynomial Properness Tau W fvec last  592450600e93 construction uses the P2 M PI Polynomial Properness Tau W fvec last  592450600e93 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/FvecCastSucc.lean#L43-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/FvecCastSucc.lean#L43-L44

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

theorem P2M_PI_PolynomialProperness_TauW_fvec_last__592450600e93 (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by sorry

alias «PI».«PolynomialProperness».«TauW».«fvec_last'» := P2M_PI_PolynomialProperness_TauW_fvec_last__592450600e93
