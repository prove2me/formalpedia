-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_scale_prod
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.Sd.scale_prod
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:26:55.998789+00:00
-- url     : https://prove2.me/theorems/25a8b228-ac6f-5a58-8d44-ff0f9b72716e
-- title:
--   Sd: scale prod
-- statement:
--   The Sd construction uses the scale prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/IsCompactDbox.lean#L27-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/IsCompactDbox.lean#L27-L53

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_DiagonalPhaseFirstVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_IsCompactDbox
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
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {V : Type} [AddCommGroup V] [Module (Fv F v) V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul (Fv F v) V] [LocallyCompactSpace V]
  [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]

theorem PI.UnitaryGroupMassFormula.LocJacTyp.Sd.scale_prod (μ0 : Measure V) [μ0.IsAddHaarMeasure] (c : Fv F v) (hc : c ≠ 0)
    (A B : Set V) (hA : MeasurableSet A) (hB : MeasurableSet B) (hA0 : μ0 A ≠ 0) (hAt : μ0 A ≠ ⊤) :
    μ0 ((fun x : V => c • x) ⁻¹' A) * μ0 ((fun x : V => c⁻¹ • x) ⁻¹' B) = μ0 A * μ0 B := by sorry
