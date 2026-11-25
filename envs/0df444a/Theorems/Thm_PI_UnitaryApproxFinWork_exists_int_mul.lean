-- Prove2me | Theorems.Thm_PI_UnitaryApproxFinWork_exists_int_mul
-- name    : PI.UnitaryApproxFinWork.exists_int_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:29.284859+00:00
-- url     : https://prove2.me/theorems/9bde7146-a6a9-484d-84c5-d91ab978e8b4
-- title:
--   Unitary Approx Fin Work: exists int mul
-- statement:
--   The Unitary Approx Fin Work construction uses the exists int mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/MemIntOEOfIsIntegral.lean#L73-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/MemIntOEOfIsIntegral.lean#L73-L77

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

theorem PI.UnitaryApproxFinWork.exists_int_mul (x : E) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ algebraMap F E (c : F) * x ∈ PI.UnitaryApproxDefs.intOE E := by sorry
