-- Prove2me | Theorems.Thm_PI_UnitaryApproxFinWork_algebraMap_mem_intOE
-- name    : PI.UnitaryApproxFinWork.algebraMap_mem_intOE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:16.872115+00:00
-- url     : https://prove2.me/theorems/246781ed-8a05-4dbc-876e-b58813328a9d
-- title:
--   Unitary Approx Fin Work: algebra Map mem int OE
-- statement:
--   The Unitary Approx Fin Work construction uses the algebra Map mem int OE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/MemIntOEOfIsIntegral.lean#L56-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/MemIntOEOfIsIntegral.lean#L56-L56

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

theorem PI.UnitaryApproxFinWork.algebraMap_mem_intOE (a : 𝓞 F) : algebraMap F E (a : F) ∈ PI.UnitaryApproxDefs.intOE E := by sorry
