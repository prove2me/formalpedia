-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_Memb_mem_spanR_of_split
-- name    : PI.UnitaryGroupMassFormula.MeasWCore.Memb.mem_spanR_of_split
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:34:27.319277+00:00
-- url     : https://prove2.me/theorems/9cb87e78-1e32-4bf2-880e-d96c40117d3e
-- title:
--   Memb: mem span R of split
-- statement:
--   The Memb construction uses the mem span R of split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedMeasureSplitting/MemSpanRIffSplit.lean#L96-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedMeasureSplitting/MemSpanRIffSplit.lean#L96-L121

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

theorem PI.UnitaryGroupMassFormula.MeasWCore.Memb.mem_spanR_of_split (hbij : Function.Bijective (splT (F := F) (E := E))) {m : ℕ}
    (Y : Fin m → Fin n → E) (s : Set (Fin m)) (w : Fin n → AF F ⊗[F] E)
    (h1 : mapV (E := E) (fstA F) w ∈ spanR (F := F) (Ainf F) Y s)
    (h2 : mapV (E := E) (sndA F) w ∈ spanR (F := F) (Af F) Y s) :
    w ∈ spanR (F := F) (AF F) Y s := by sorry
