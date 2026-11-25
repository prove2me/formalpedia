-- Prove2me | Theorems.Thm_PI_UnitaryApproxFinWork_dv_mem_Sv
-- name    : PI.UnitaryApproxFinWork.dv_mem_Sv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:30:49.281956+00:00
-- url     : https://prove2.me/theorems/a59ee96b-b906-4388-a095-4aef27758ef8
-- title:
--   Unitary Approx Fin Work: dv mem Sv
-- statement:
--   The Unitary Approx Fin Work construction uses the dv mem Sv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/MemIntOEOfIsIntegral.lean#L85-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/MemIntOEOfIsIntegral.lean#L85-L85

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

theorem PI.UnitaryApproxFinWork.dv_mem_Sv (v : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F) : dv E v d ∈ Sv E v := by sorry
