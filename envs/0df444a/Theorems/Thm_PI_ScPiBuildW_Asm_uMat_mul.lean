-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Asm_uMat_mul
-- name    : PI.ScPiBuildW.Asm.uMat_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:26:58.742737+00:00
-- url     : https://prove2.me/theorems/ab2152c9-fd6f-4c55-8957-06702aea2800
-- title:
--   Asm: u Mat mul
-- statement:
--   The Asm construction uses the u Mat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/InnerOfNorm.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/InnerOfNorm.lean#L22-L23

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocFrame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_ContinuousOnTensOp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_InnerOfNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open scoped InnerProductSpace
open PI PI.ScPiBuildW PI.ScPiBuildW.Asm
open PI.ScPiExists Formalism.MainNotions.S

theorem PI.ScPiBuildW.Asm.uMat_mul (I : AutInst) (s t : I.Ginf) (v : InfinitePlace I.F) :
    uMat ((s * t) v) = uMat (s v) * uMat (t v) := by sorry
