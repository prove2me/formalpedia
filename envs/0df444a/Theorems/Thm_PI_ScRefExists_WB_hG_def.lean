-- Prove2me | Theorems.Thm_PI_ScRefExists_WB_hG_def
-- name    : PI.ScRefExists.WB.hG_def
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:16:41.585793+00:00
-- url     : https://prove2.me/theorems/3a83a65d-38c9-4d86-adfa-813c9f52d07a
-- title:
--   WB: h G def
-- statement:
--   The WB construction uses the h G def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HGZeroRight.lean#L13-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HGZeroRight.lean#L13-L13

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

theorem PI.ScRefExists.WB.hG_def (x y : Fin I.n → I.E) : hG I x y = ∑ i, ∑ j, star (x i) * I.J i j * y j := by sorry
