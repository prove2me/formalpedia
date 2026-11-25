-- Prove2me | Theorems.Thm_PI_Dv_ProjAW_one_sub_idem
-- name    : PI.Dv.ProjAW.one_sub_idem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:28:22.79819+00:00
-- url     : https://prove2.me/theorems/dd1899d8-0c5b-42b9-8e0e-ec70d1840cf0
-- title:
--   Proj AW: one sub idem
-- statement:
--   The Proj AW construction uses the one sub idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LengthIndex/LenAtEqZero.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LengthIndex/LenAtEqZero.lean#L29-L30

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

theorem PI.Dv.ProjAW.one_sub_idem {f : Module.End K A.V} (hf : f * f = f) : (1 - f) * (1 - f) = 1 - f := by sorry
