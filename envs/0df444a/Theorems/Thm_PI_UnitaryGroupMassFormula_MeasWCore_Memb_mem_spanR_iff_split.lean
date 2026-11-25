-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_Memb_mem_spanR_iff_split
-- name    : PI.UnitaryGroupMassFormula.MeasWCore.Memb.mem_spanR_iff_split
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:32:54.928004+00:00
-- url     : https://prove2.me/theorems/773c718f-b1b7-54d6-82c8-84852cd1c98c
-- title:
--   Memb: mem span R iff split
-- statement:
--   The Memb construction uses the mem span R iff split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedMeasureSplitting/MemSpanRIffSplit.lean#L123-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedMeasureSplitting/MemSpanRIffSplit.lean#L123-L128

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

theorem PI.UnitaryGroupMassFormula.MeasWCore.Memb.mem_spanR_iff_split (hbij : Function.Bijective (splT (F := F) (E := E))) {m : ℕ}
    (Y : Fin m → Fin n → E) (s : Set (Fin m)) (w : Fin n → AF F ⊗[F] E) :
    w ∈ spanR (F := F) (AF F) Y s ↔ mapV (E := E) (fstA F) w ∈ spanR (F := F) (Ainf F) Y s ∧
      mapV (E := E) (sndA F) w ∈ spanR (F := F) (Af F) Y s := by sorry
