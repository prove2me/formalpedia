-- Prove2me | Theorems.Thm_PI_SelfDualBridge_W_dualAt_of_equiv
-- name    : PI.SelfDualBridge.W.dualAt_of_equiv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:25:54.681579+00:00
-- url     : https://prove2.me/theorems/3d4f6edb-259b-4dd7-a06e-678a0ecbc2bc
-- title:
--   W: dual At of equiv
-- statement:
--   The W construction uses the dual At of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualContinuity/ContinuousReTupSymm.lean#L23-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualContinuity/ContinuousReTupSymm.lean#L23-L53

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
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem PI.SelfDualBridge.W.dualAt_of_equiv {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [AddCommGroup V']
    [TopologicalSpace V'] (e : V ≃+ V') (he : Continuous e) (hes : Continuous e.symm)
    (B : V → V → Fv F v) (B' : V' → V' → Fv F v) (hB : ∀ x y, B x y = B' (e x) (e y))
    (h : DualAt v B') : DualAt v B := by sorry
