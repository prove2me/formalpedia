-- Prove2me | Theorems.Thm_PI_UnitaryApproxFinWork_sigR_inclE
-- name    : PI.UnitaryApproxFinWork.sigR_inclE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:31.686178+00:00
-- url     : https://prove2.me/theorems/8fc16172-4bad-4a7d-842c-386538f96f38
-- title:
--   Unitary Approx Fin Work: sig R incl E
-- statement:
--   The Unitary Approx Fin Work construction uses the sig R incl E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/MemIntOEOfIsIntegral.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/MemIntOEOfIsIntegral.lean#L44-L48

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
variable {F E : Type} [Field F] [CommRing E] [Algebra F E]

theorem PI.UnitaryApproxFinWork.sigR_inclE (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (e : E) :
    PI.UnitaryApproxDefs.sigR σ R (PI.UnitaryApproxDefs.inclE (F := F) R e) = PI.UnitaryApproxDefs.inclE (F := F) R (σ e) := by sorry
