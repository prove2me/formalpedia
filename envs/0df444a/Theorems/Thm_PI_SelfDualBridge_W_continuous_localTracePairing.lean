-- Prove2me | Theorems.Thm_PI_SelfDualBridge_W_continuous_localTracePairing
-- name    : PI.SelfDualBridge.W.continuous_localTracePairing
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:24:03.726147+00:00
-- url     : https://prove2.me/theorems/7a1cb6b8-f1e2-426e-8559-fcc52e6c7e92
-- title:
--   W: continuous local Trace Pairing
-- statement:
--   The W construction uses the continuous local Trace Pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualContinuity/ContinuousReTupSymm.lean#L124-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualContinuity/ContinuousReTupSymm.lean#L124-L132

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualBridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_AdditiveCharacterNontrivial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualContinuity_ContinuousReTupSymm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SelfDualBridge PI.SelfDualBridge.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.Sd PI.OmFibreUniq.W.SdAbs
open PI.VolStabSW PI.VolStabSW.SdUniqW PI.VolStabSW.SdDualW PI.AdicCompletionValuation
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem PI.SelfDualBridge.W.continuous_localTracePairing (ι : Type) [Fintype ι] :
    Continuous (fun p : (ι → Fv F v ⊗[F] E) × (ι → Fv F v ⊗[F] E) => trP v ι p.1 p.2) := by sorry
