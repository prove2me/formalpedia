-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_sdE_eq
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.Sd.sdE_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:37.501808+00:00
-- url     : https://prove2.me/theorems/7212969c-5a54-4830-bfd1-ee64b9b6f780
-- title:
--   Sd: sd E eq
-- statement:
--   The Sd construction uses the sd E eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ChiZeroRight.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ChiZeroRight.lean#L22-L24

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousPsiVOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ChiZeroRight
import Theorems.Thm_PI_VolStabSW_locallyCompact_Fv
import Theorems.Thm_PI_VolStabSW_secondCountable_Fv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp PI.UnitaryGroupMassFormula.LocJacTyp.Sd
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open PI.VolStabSW.SdUniqW
open scoped TensorProduct
attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ)
open Classical

theorem PI.UnitaryGroupMassFormula.LocJacTyp.Sd.sdE_eq (ι : Type) [Fintype ι] :
    sdE (E := E) ψ v ι = if h : ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ (chi (E := E) v ψ ι)
      then h.choose else 0 := by sorry
