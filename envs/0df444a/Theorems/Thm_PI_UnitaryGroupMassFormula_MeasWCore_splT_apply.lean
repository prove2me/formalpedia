-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_splT_apply
-- name    : PI.UnitaryGroupMassFormula.MeasWCore.splT_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:39:00.952604+00:00
-- url     : https://prove2.me/theorems/4f86ca66-2b44-48b5-a97a-1b67e09c7f71
-- title:
--   Meas WCore: spl T apply
-- statement:
--   The Meas WCore construction uses the spl T apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedMeasureSplitting/SplTApply.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedMeasureSplitting/SplTApply.lean#L16-L17

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_Measures
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_SplTApply
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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures NumberField
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem PI.UnitaryGroupMassFormula.MeasWCore.splT_apply (x : AF F ⊗[F] E) :
    splT x = (tensMap (E := E) (fstA F) x, tensMap (E := E) (sndA F) x) := by sorry
