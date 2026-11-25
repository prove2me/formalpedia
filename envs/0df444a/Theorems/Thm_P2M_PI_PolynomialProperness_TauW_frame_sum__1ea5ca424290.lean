-- Prove2me | Theorems.Thm_P2M_PI_PolynomialProperness_TauW_frame_sum__1ea5ca424290
-- name    : P2M_PI_PolynomialProperness_TauW_frame_sum__1ea5ca424290
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:57:42.350488+00:00
-- url     : https://prove2.me/theorems/5c14f876-8c97-4577-943f-9203b627cf37
-- title:
--   P2 M PI Polynomial Properness Tau W frame sum  1ea5ca424290: P2 M PI Polynomial Properness Tau W frame sum  1ea5ca424290
-- statement:
--   The P2 M PI Polynomial Properness Tau W frame sum  1ea5ca424290 construction uses the P2 M PI Polynomial Properness Tau W frame sum  1ea5ca424290 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/FvecCastSucc.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/FvecCastSucc.lean#L46-L49

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

theorem P2M_PI_PolynomialProperness_TauW_frame_sum__1ea5ca424290 (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (r + 1) → ℂ) :
    ∑ a, c a • fvec k r z a = ∑ b : Fin r, c b.castSucc • bvec (eI k r b) + c (Fin.last r) • z := by sorry

alias «PI».«PolynomialProperness».«TauW».«frame_sum'» := P2M_PI_PolynomialProperness_TauW_frame_sum__1ea5ca424290
