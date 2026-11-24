-- Prove2me | Theorems.Thm_PI_ScRefExists_WF_hG_add_left
-- name    : PI.ScRefExists.WF.hG_add_left
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:59:09.102664+00:00
-- url     : https://prove2.me/theorems/7ce6d1d5-a742-4f1d-9790-b3c6d0f9c03d
-- title:
--   WF: h G add left
-- statement:
--   The WF construction uses the h G add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/StarMemAp.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/StarMemAp.lean#L17-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_StarMemAp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk
open Matrix
open PI PI.ScRefExists PI.ScRefExists.WF
variable (I : Formalism.MainNotions.S.AutInst)

theorem PI.ScRefExists.WF.hG_add_left (x y z : Fin I.n → I.E) : hG I (x + y) z = hG I x z + hG I y z := by sorry
