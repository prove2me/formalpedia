-- Prove2me | Theorems.Thm_P2M_PI_PolynomialProperness_TauW_fvec_castSucc__9e5f4a85106f
-- name    : P2M_PI_PolynomialProperness_TauW_fvec_castSucc__9e5f4a85106f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:52:36.590866+00:00
-- url     : https://prove2.me/theorems/fab7832c-0f3e-46aa-9517-db2b8c7243dc
-- title:
--   P2 M PI Polynomial Properness Tau W fvec cast Succ  9e5f4a85106f: P2 M PI Polynomial Properness Tau W fvec cast Succ  9e5f4a85106f
-- statement:
--   The P2 M PI Polynomial Properness Tau W fvec cast Succ  9e5f4a85106f construction uses the P2 M PI Polynomial Properness Tau W fvec cast Succ  9e5f4a85106f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/FvecCastSucc.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/FvecCastSucc.lean#L39-L41

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

theorem P2M_PI_PolynomialProperness_TauW_fvec_castSucc__9e5f4a85106f (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    fvec k r z b.castSucc = bvec (eI k r b) := by sorry

alias «PI».«PolynomialProperness».«TauW».«fvec_castSucc'» := P2M_PI_PolynomialProperness_TauW_fvec_castSucc__9e5f4a85106f
