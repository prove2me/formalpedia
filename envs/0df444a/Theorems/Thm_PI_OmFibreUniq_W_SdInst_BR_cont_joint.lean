-- Prove2me | Theorems.Thm_PI_OmFibreUniq_W_SdInst_BR_cont_joint
-- name    : PI.OmFibreUniq.W.SdInst.BR_cont_joint
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:37:28.975176+00:00
-- url     : https://prove2.me/theorems/9b7504ad-bcfa-4fd6-b326-8f34ba437bc0
-- title:
--   Sd Inst: BR cont joint
-- statement:
--   The Sd Inst construction uses the BR cont joint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SdExInst.lean#L61-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SdExInst.lean#L61-L83

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExInst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.SdInst
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.Sd PI.OmFibreUniq.W.SdAbs
open PI.VolStabSW PI.VolStabSW.SdUniqW PI.VolStabSW.SdDualW PI.AdicCompletionValuation
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem PI.OmFibreUniq.W.SdInst.BR_cont_joint (σ : E →ₐ[F] E) {n a : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    Continuous (fun p : (Fin a → Fin n → Fv F v ⊗[F] E) × (Fin a → Fin n → Fv F v ⊗[F] E) =>
      BR (Fv F v) σ J p.1 p.2) := by sorry
