-- Prove2me | Theorems.Thm_PI_ScRefExists_PPA_hG_add_right
-- name    : PI.ScRefExists.PPA.hG_add_right
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:22:55.660015+00:00
-- url     : https://prove2.me/theorems/34db819b-5421-491a-b350-b4959e70398b
-- title:
--   PPA: h G add right
-- statement:
--   The PPA construction uses the h G add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/NatCastSmulMemL.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/NatCastSmulMemL.lean#L17-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_NatCastSmulMemL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open PI PI.ScRefExists PI.ScRefExists.PPA
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)

theorem PI.ScRefExists.PPA.hG_add_right (x y y' : Fin I.n → I.E) : hG I x (y + y') = hG I x y + hG I x y' := by sorry
