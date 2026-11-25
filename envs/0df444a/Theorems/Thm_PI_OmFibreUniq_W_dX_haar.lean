-- Prove2me | Theorems.Thm_PI_OmFibreUniq_W_dX_haar
-- name    : PI.OmFibreUniq.W.dX_haar
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:15:17.351616+00:00
-- url     : https://prove2.me/theorems/7787c95c-2336-44fc-9ed2-b23ad1c6324e
-- title:
--   W: d X haar
-- statement:
--   The W construction uses the d X haar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/Development.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/Development.lean#L44-L48

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OmFibreUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open PI.OmFibreUniq
open scoped TensorProduct Classical
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (a : ℕ)

theorem PI.OmFibreUniq.W.dX_haar (h : ∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) :
    (dX σ J ψ v a).IsAddHaarMeasure := by sorry
