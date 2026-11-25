-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_mem_Nsub_iff
-- name    : PI.UnitaryGroupMassFormula.MeasWCore.mem_Nsub_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:34.23047+00:00
-- url     : https://prove2.me/theorems/9b209fef-fd77-4b1b-a235-270e8624e332
-- title:
--   Meas WCore: mem Nsub iff
-- statement:
--   The Meas WCore construction uses the mem Nsub iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedMeasureSplitting/MemSpanRIffSplit.lean#L174-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedMeasureSplitting/MemSpanRIffSplit.lean#L174-L231

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
open Memb
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

theorem PI.UnitaryGroupMassFormula.MeasWCore.mem_Nsub_iff (hbij : Function.Bijective (splT (F := F) (E := E))) {r : ℕ} (P : Frame E n r)
    (g : HA (AF F) σ J) :
    g ∈ Nsub (AF F) σ J P ↔ haMap σ J (fstA F) g ∈ Nsub (Ainf F) σ J P ∧
      haMap σ J (sndA F) g ∈ Nsub (Af F) σ J P := by sorry
