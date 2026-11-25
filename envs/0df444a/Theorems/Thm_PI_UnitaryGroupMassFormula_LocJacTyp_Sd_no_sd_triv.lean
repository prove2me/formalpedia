-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_no_sd_triv
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.Sd.no_sd_triv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:17:30.852011+00:00
-- url     : https://prove2.me/theorems/7211b99b-6e10-580b-97ce-71eda17b1999
-- title:
--   Sd: no sd triv
-- statement:
--   The Sd construction uses the no sd triv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ComponentsOfD1EqZero.lean#L50-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ComponentsOfD1EqZero.lean#L50-L87

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ChiZeroRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ComponentsOfD1EqZero
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
variable [SecondCountableTopology (Fv F v ⊗[F] E)]

theorem PI.UnitaryGroupMassFormula.LocJacTyp.Sd.no_sd_triv (ι : Type) [Fintype ι] [Nonempty ι] (htriv : ∀ r, psiV F ψ v r = 1) :
    ¬ ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ (chi (E := E) v ψ ι) := by sorry
