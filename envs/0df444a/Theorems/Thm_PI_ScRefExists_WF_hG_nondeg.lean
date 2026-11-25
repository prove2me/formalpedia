-- Prove2me | Theorems.Thm_PI_ScRefExists_WF_hG_nondeg
-- name    : PI.ScRefExists.WF.hG_nondeg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:42:52.417323+00:00
-- url     : https://prove2.me/theorems/1b593c36-f944-503a-9ab6-f521fabd46b2
-- title:
--   WF: h G nondeg
-- statement:
--   The WF construction uses the h G nondeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/StarMemAp.lean#L79-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/StarMemAp.lean#L79-L83

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

theorem PI.ScRefExists.WF.hG_nondeg (v : Fin I.n → I.E) (h : ∀ x, hG I x v = 0) : v = 0 := by sorry
