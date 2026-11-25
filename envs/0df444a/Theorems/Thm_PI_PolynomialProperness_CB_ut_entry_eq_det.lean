-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CB_ut_entry_eq_det
-- name    : PI.PolynomialProperness.CB.ut_entry_eq_det
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:07.409414+00:00
-- url     : https://prove2.me/theorems/d8434bea-929c-544d-88c6-975a2c829807
-- title:
--   CB: ut entry eq det
-- statement:
--   The CB construction uses the ut entry eq det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/SecondOrderNormBound.lean#L33-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/SecondOrderNormBound.lean#L33-L69

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

theorem PI.PolynomialProperness.CB.ut_entry_eq_det {m : ℕ} {L U : Matrix (Fin m) (Fin m) ℂ} (hL : L ∈ LTset m)
    (hU : U ∈ UTset m) (i j : Fin m) : U i j = ((L * U).submatrix (rws i) (cls i j)).det := by sorry
