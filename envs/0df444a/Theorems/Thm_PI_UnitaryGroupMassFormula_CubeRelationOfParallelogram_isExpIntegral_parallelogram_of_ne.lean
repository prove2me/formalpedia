-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_isExpIntegral_parallelogram_of_ne
-- name    : PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.isExpIntegral_parallelogram_of_ne
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:39:11.356134+00:00
-- url     : https://prove2.me/theorems/45cc3155-49b1-40a5-9f54-2a6dae23368a
-- title:
--   Cube Relation Of Parallelogram: is Exp Integral parallelogram of ne
-- statement:
--   The Cube Relation Of Parallelogram construction uses the is Exp Integral parallelogram of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubeFormalIdentities/IsExpIntegralParallelogramOfNe.lean#L168-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubeFormalIdentities/IsExpIntegralParallelogramOfNe.lean#L168-L196

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_IsExpIntegralParallelogramOfNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
open PI.FglGram MvPowerSeries
variable {p : ℕ} [Fact p.Prime] {σ τ : Type*}
variable {l ex : PowerSeries ℂ_[p]} (ph : PowerSeries ℂ_[p])
  (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.constantCoeff l = 0)
include hex hl

theorem PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.isExpIntegral_parallelogram_of_ne (i j : Fin 3) (hij : i ≠ j)
    (hE1 : Simeq (phAt ph (add l ex (Xv 0) (Xv 1)) + phAt ph (sub l ex (Xv 0) (Xv 1)) :
        MvPowerSeries (Fin 2) ℂ_[p]) (2 * phAt ph (Xv 0) + 2 * phAt ph (Xv 1))) :
    Good (phAt ph (add l ex (Xv i) (Xv j)) + phAt ph (sub l ex (Xv i) (Xv j)) -
      (2 * phAt ph (Xv i) + 2 * phAt ph (Xv j)) : MvPowerSeries (Fin 3) ℂ_[p]) := by sorry
