-- Prove2me | Theorems.Thm_PI_ScRefExists_PPA_QA_neg
-- name    : PI.ScRefExists.PPA.QA_neg
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:48.576041+00:00
-- url     : https://prove2.me/theorems/8f9fcbde-e56e-4508-8b71-8cfaff47fc27
-- title:
--   PPA: QA neg
-- statement:
--   The PPA construction uses the QA neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/NatCastSmulMemL.lean#L170-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/NatCastSmulMemL.lean#L170-L174

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

theorem PI.ScRefExists.PPA.QA_neg (p q : ℕ) {x : I.E} (hx : QA I p q x) : QA I p q (-x) := by sorry
