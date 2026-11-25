-- Prove2me | Theorems.Thm_PI_FJMB_pderiv_aeval_killS
-- name    : PI.FJMB.pderiv_aeval_killS
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:37.602619+00:00
-- url     : https://prove2.me/theorems/b0ff7ae1-8ace-495e-b0e9-f47414c30b2d
-- title:
--   FJMB: pderiv aeval kill S
-- statement:
--   The FJMB construction uses the pderiv aeval kill S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurElim.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurElim.lean#L41-L47

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
open PI PI.FJMB
variable {σ : Type*}

theorem PI.FJMB.pderiv_aeval_killS (S : Set σ) (w : σ) (hw : w ∉ S) (f : MvPolynomial σ ℂ) :
    pderiv w (aeval (killS S) f) = aeval (killS S) (pderiv w f) := by sorry
