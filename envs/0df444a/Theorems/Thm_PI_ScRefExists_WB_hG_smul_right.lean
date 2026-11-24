-- Prove2me | Theorems.Thm_PI_ScRefExists_WB_hG_smul_right
-- name    : PI.ScRefExists.WB.hG_smul_right
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:18:02.519196+00:00
-- url     : https://prove2.me/theorems/f33901f2-66aa-47fd-9245-3f9640dd2be8
-- title:
--   WB: h G smul right
-- statement:
--   The WB construction uses the h G smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HGZeroRight.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HGZeroRight.lean#L23-L26

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

theorem PI.ScRefExists.WB.hG_smul_right (c : I.E) (x y : Fin I.n → I.E) : hG I x (c • y) = c * hG I x y := by sorry
