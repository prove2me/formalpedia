-- Prove2me | Theorems.Thm_P2M_PI_Dv_ProjGramW_dvProjGram_of__4fc85b4471e1
-- name    : P2M_PI_Dv_ProjGramW_dvProjGram_of__4fc85b4471e1
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:56:36.902004+00:00
-- url     : https://prove2.me/theorems/ed2596ca-1b92-4e49-bf34-4b64e884e2e6
-- title:
--   P2 M PI Dv Proj Gram W dv Proj Gram of  4fc85b4471e1: P2 M PI Dv Proj Gram W dv Proj Gram of  4fc85b4471e1
-- statement:
--   The P2 M PI Dv Proj Gram W dv Proj Gram of  4fc85b4471e1 construction uses the P2 M PI Dv Proj Gram W dv Proj Gram of  4fc85b4471e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/DvProjGramOf.lean#L11-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/DvProjGramOf.lean#L11-L196

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_DvProjGramOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions

theorem P2M_PI_Dv_ProjGramW_dvProjGram_of__4fc85b4471e1 (hA : ProjA) (hI : IdxCalc) (hD : IdxDet) : gram_det_kernel_base_level := by sorry

alias «PI».«Dv».«ProjGramW».«dvProjGram_of'» := P2M_PI_Dv_ProjGramW_dvProjGram_of__4fc85b4471e1
