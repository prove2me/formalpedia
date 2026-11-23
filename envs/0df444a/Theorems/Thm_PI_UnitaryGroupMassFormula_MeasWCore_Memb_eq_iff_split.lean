-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_Memb_eq_iff_split
-- name    : PI.UnitaryGroupMassFormula.MeasWCore.Memb.eq_iff_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:14.15331+00:00
-- url     : https://prove2.me/theorems/d8151af7-0507-4274-98ab-031a60815072
-- title:
--   Memb: eq iff split
-- statement:
--   The Memb construction uses the eq iff split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedMeasureSplitting/MemSpanRIffSplit.lean#L75-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedMeasureSplitting/MemSpanRIffSplit.lean#L75-L86

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_SplTApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_MemSpanRIffSplit
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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures NumberField
open scoped TensorProduct
open PI.UnitaryGroupMassFormula.MeasWCore.Memb
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem PI.UnitaryGroupMassFormula.MeasWCore.Memb.eq_iff_split (hinj : Function.Injective (splT (F := F) (E := E)))
    (w u : Fin n → AF F ⊗[F] E) :
    w = u ↔ mapV (E := E) (fstA F) w = mapV (E := E) (fstA F) u ∧
      mapV (E := E) (sndA F) w = mapV (E := E) (sndA F) u := by sorry
