-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_mem_Hsub_iff
-- name    : PI.UnitaryGroupMassFormula.MeasWCore.mem_Hsub_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:33:27.277829+00:00
-- url     : https://prove2.me/theorems/93094e8f-21a9-5483-9192-d8c227c7c8de
-- title:
--   Meas WCore: mem Hsub iff
-- statement:
--   The Meas WCore construction uses the mem Hsub iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedMeasureSplitting/MemSpanRIffSplit.lean#L155-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedMeasureSplitting/MemSpanRIffSplit.lean#L155-L172

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

theorem PI.UnitaryGroupMassFormula.MeasWCore.mem_Hsub_iff (hinj : Function.Injective (splT (F := F) (E := E))) {r : ℕ} (P : Frame E n r)
    (g : HA (AF F) σ J) :
    g ∈ Hsub (AF F) σ J P ↔ haMap σ J (fstA F) g ∈ Hsub (Ainf F) σ J P ∧
      haMap σ J (sndA F) g ∈ Hsub (Af F) σ J P := by sorry
