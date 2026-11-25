-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CB_det_ut
-- name    : PI.PolynomialProperness.CB.det_ut
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:59:22.426837+00:00
-- url     : https://prove2.me/theorems/7b1071c9-2104-407c-af0b-85801242dde0
-- title:
--   CB: det ut
-- statement:
--   The CB construction uses the det ut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/SecondOrderNormBound.lean#L101-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/SecondOrderNormBound.lean#L101-L104

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_SecondOrderNormBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.CB

theorem PI.PolynomialProperness.CB.det_ut {m : ℕ} {U : Matrix (Fin m) (Fin m) ℂ} (hU : U ∈ UTset m) : U.det = 1 := by sorry
