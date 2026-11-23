-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_Memb_mapV_apply
-- name    : PI.UnitaryGroupMassFormula.MeasWCore.Memb.mapV_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:34.652817+00:00
-- url     : https://prove2.me/theorems/68bdf962-6518-48b4-b8b8-0d4ec2414173
-- title:
--   Memb: map V apply
-- statement:
--   The Memb construction uses the map V apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedMeasureSplitting/MemSpanRIffSplit.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedMeasureSplitting/MemSpanRIffSplit.lean#L21-L22

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
variable {F E : Type} [Field F] [Field E] [Algebra F E]
  {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (φ : R →ₐ[F] R') {n : ℕ}

theorem PI.UnitaryGroupMassFormula.MeasWCore.Memb.mapV_apply (x : Fin n → R ⊗[F] E) (i : Fin n) :
    mapV (E := E) φ x i = tensMap (E := E) φ (x i) := by sorry

attribute [defeq] PI.UnitaryGroupMassFormula.MeasWCore.Memb.mapV_apply
