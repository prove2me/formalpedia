-- Prove2me | Theorems.Thm_PI_UnitaryApproxFinWork_dv_mul
-- name    : PI.UnitaryApproxFinWork.dv_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:31.751715+00:00
-- url     : https://prove2.me/theorems/2140aa27-5e96-44bf-8e61-cb5174d4cfc9
-- title:
--   Unitary Approx Fin Work: dv mul
-- statement:
--   The Unitary Approx Fin Work construction uses the dv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/MemIntOEOfIsIntegral.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/MemIntOEOfIsIntegral.lean#L87-L89

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

theorem PI.UnitaryApproxFinWork.dv_mul (v : HeightOneSpectrum (𝓞 F)) (a b : 𝓞 F) : dv E v (a * b) = dv E v a * dv E v b := by sorry
