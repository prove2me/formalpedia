-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_Memb_hR_mapV
-- name    : PI.UnitaryGroupMassFormula.MeasWCore.Memb.hR_mapV
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:32:51.396819+00:00
-- url     : https://prove2.me/theorems/cf91eac3-0a48-4b3c-a679-9fd30cc472c2
-- title:
--   Memb: h R map V
-- statement:
--   The Memb construction uses the h R map V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedMeasureSplitting/MemSpanRIffSplit.lean#L56-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedMeasureSplitting/MemSpanRIffSplit.lean#L56-L64

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
variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

theorem PI.UnitaryGroupMassFormula.MeasWCore.Memb.hR_mapV (x y : Fin n → R ⊗[F] E) :
    hR R' σ J (mapV (E := E) φ x) (mapV (E := E) φ y) = tensMap (E := E) φ (hR R σ J x y) := by sorry
