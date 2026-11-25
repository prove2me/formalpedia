-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_Memb_exists_split
-- name    : PI.UnitaryGroupMassFormula.MeasWCore.Memb.exists_split
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:33:09.417701+00:00
-- url     : https://prove2.me/theorems/d10c53ba-bbe0-4b18-a511-b1f7cc5191f4
-- title:
--   Memb: exists split
-- statement:
--   The Memb construction uses the exists split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedMeasureSplitting/MemSpanRIffSplit.lean#L88-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedMeasureSplitting/MemSpanRIffSplit.lean#L88-L94

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

theorem PI.UnitaryGroupMassFormula.MeasWCore.Memb.exists_split (hsurj : Function.Surjective (splT (F := F) (E := E)))
    (y₁ : Fin n → Ainf F ⊗[F] E) (y₂ : Fin n → Af F ⊗[F] E) :
    ∃ v : Fin n → AF F ⊗[F] E, mapV (E := E) (fstA F) v = y₁ ∧ mapV (E := E) (sndA F) v = y₂ := by sorry
