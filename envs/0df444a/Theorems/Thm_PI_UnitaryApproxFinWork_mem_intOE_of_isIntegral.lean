-- Prove2me | Theorems.Thm_PI_UnitaryApproxFinWork_mem_intOE_of_isIntegral
-- name    : PI.UnitaryApproxFinWork.mem_intOE_of_isIntegral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:01.894799+00:00
-- url     : https://prove2.me/theorems/96c47ce9-33e9-481e-9aee-a73cb715bcc2
-- title:
--   Unitary Approx Fin Work: mem int OE of is Integral
-- statement:
--   The Unitary Approx Fin Work construction uses the mem int OE of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/MemIntOEOfIsIntegral.lean#L54-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/MemIntOEOfIsIntegral.lean#L54-L54

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open PI PI.UnitaryApproxFinWork
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem PI.UnitaryApproxFinWork.mem_intOE_of_isIntegral {x : E} (h : IsIntegral ℤ x) : x ∈ PI.UnitaryApproxDefs.intOE E := by sorry
