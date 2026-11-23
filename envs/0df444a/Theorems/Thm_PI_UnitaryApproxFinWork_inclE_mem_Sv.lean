-- Prove2me | Theorems.Thm_PI_UnitaryApproxFinWork_inclE_mem_Sv
-- name    : PI.UnitaryApproxFinWork.inclE_mem_Sv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:09.178171+00:00
-- url     : https://prove2.me/theorems/a643c06b-b14b-4a9e-ab6b-6d8e61187793
-- title:
--   Unitary Approx Fin Work: incl E mem Sv
-- statement:
--   The Unitary Approx Fin Work construction uses the incl E mem Sv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/MemIntOEOfIsIntegral.lean#L79-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/MemIntOEOfIsIntegral.lean#L79-L80

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

theorem PI.UnitaryApproxFinWork.inclE_mem_Sv (v : HeightOneSpectrum (𝓞 F)) {x : E} (hx : x ∈ PI.UnitaryApproxDefs.intOE E) :
    PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) x ∈ Sv E v := by sorry
