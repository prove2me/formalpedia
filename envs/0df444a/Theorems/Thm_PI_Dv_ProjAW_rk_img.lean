-- Prove2me | Theorems.Thm_PI_Dv_ProjAW_rk_img
-- name    : PI.Dv.ProjAW.rk_img
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:28:16.911509+00:00
-- url     : https://prove2.me/theorems/176ddede-bbb9-48ec-b542-647d8067fbde
-- title:
--   Proj AW: rk img
-- statement:
--   The Proj AW construction uses the rk img property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LengthIndex/LenAtEqZero.lean#L80-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LengthIndex/LenAtEqZero.lean#L80-L82

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_LenAtEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjAW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (A : HLat K)

theorem PI.Dv.ProjAW.rk_img (hG : A.Good) (f : Module.End K A.V) : Formalism.HN.rkK (imgE A f A.L) = dimE A f := by sorry
