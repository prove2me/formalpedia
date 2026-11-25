-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_splR_apply
-- name    : PI.UnitaryGroupMassFormula.MeasWCore.splR_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:33:19.215803+00:00
-- url     : https://prove2.me/theorems/25a4e529-948f-4dbb-ae5b-cce819bc3ae0
-- title:
--   Meas WCore: spl R apply
-- statement:
--   The Meas WCore construction uses the spl R apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedMeasureSplitting/ContinuousTensMap.lean#L107-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedMeasureSplitting/ContinuousTensMap.lean#L107-L107

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_SplTApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_ContinuousTensMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.MeasWCore
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures NumberField Topology
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem PI.UnitaryGroupMassFormula.MeasWCore.splR_apply (x : AF F ⊗[F] E) : splR x = splT x := by sorry
