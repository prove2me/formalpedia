-- Prove2me | Theorems.Thm_PI_ScRefExists_PPA_hG_sub_right
-- name    : PI.ScRefExists.PPA.hG_sub_right
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:22:21.416952+00:00
-- url     : https://prove2.me/theorems/2a856556-5338-40ab-b1e6-53d96a126c57
-- title:
--   PPA: h G sub right
-- statement:
--   The PPA construction uses the h G sub right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/NatCastSmulMemL.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/NatCastSmulMemL.lean#L39-L40

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

theorem PI.ScRefExists.PPA.hG_sub_right (x y y' : Fin I.n → I.E) : hG I x (y - y') = hG I x y - hG I x y' := by sorry
