-- Prove2me | Theorems.Thm_PI_ScRefExists_WB_hG_zero_right
-- name    : PI.ScRefExists.WB.hG_zero_right
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:16:24.066802+00:00
-- url     : https://prove2.me/theorems/909f7912-a1c9-4dee-a897-4c3c91477fa3
-- title:
--   WB: h G zero right
-- statement:
--   The WB construction uses the h G zero right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HGZeroRight.lean#L28-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HGZeroRight.lean#L28-L28

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HGZeroRight
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
open PI PI.ScRefExists PI.ScRefExists.WB
variable (I : Formalism.MainNotions.S.AutInst)

theorem PI.ScRefExists.WB.hG_zero_right (x : Fin I.n → I.E) : hG I x 0 = 0 := by sorry
