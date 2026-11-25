-- Prove2me | Theorems.Thm_PI_UnitaryApproxFinWork_sigR_dv
-- name    : PI.UnitaryApproxFinWork.sigR_dv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:30:27.777503+00:00
-- url     : https://prove2.me/theorems/47471911-4446-5c51-af36-0a79129bdefc
-- title:
--   Unitary Approx Fin Work: sig R dv
-- statement:
--   The Unitary Approx Fin Work construction uses the sig R dv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/SigmaMemIntOE.lean#L139-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/SigmaMemIntOE.lean#L139-L140

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_SigmaMemIntOE
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
variable {n : Type} [Fintype n] [DecidableEq n]
variable {v : HeightOneSpectrum (𝓞 F)}

theorem PI.UnitaryApproxFinWork.sigR_dv (σ : E →ₐ[F] E) (d : 𝓞 F) : PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (dv E v d) = dv E v d := by sorry
