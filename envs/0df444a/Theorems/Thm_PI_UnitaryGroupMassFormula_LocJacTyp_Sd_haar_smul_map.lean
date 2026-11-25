-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_haar_smul_map
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.Sd.haar_smul_map
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:04:25.899473+00:00
-- url     : https://prove2.me/theorems/acba87a8-b560-58a0-8087-6412c1da6fb8
-- title:
--   Sd: haar smul map
-- statement:
--   The Sd construction uses the haar smul map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/IsCompactDbox.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/IsCompactDbox.lean#L21-L25

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

theorem PI.UnitaryGroupMassFormula.LocJacTyp.Sd.haar_smul_map (μ0 : Measure V) [μ0.IsAddHaarMeasure] (c : Fv F v) (hc : c ≠ 0) :
    (Measure.map (fun x : V => c • x) μ0).IsAddHaarMeasure := by sorry
