-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_reindex
-- name    : PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.reindex
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:39:03.595597+00:00
-- url     : https://prove2.me/theorems/161eb50f-23ad-4900-ad8e-bce67255f884
-- title:
--   Cube Relation Of Parallelogram: reindex
-- statement:
--   The Cube Relation Of Parallelogram construction uses the reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubeFormalIdentities/CoeffPowMulPowEqZero.lean#L94-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubeFormalIdentities/CoeffPowMulPowEqZero.lean#L94-L113

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
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
variable {p : ℕ} [Fact p.Prime] {σ : Type*}

theorem PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.reindex {M : Type*} [AddCommMonoid M] (N : ℕ) (g : ℕ → ℕ → M)
    (hg : ∀ i j, N < i + j → g i j = 0) :
    ∑ n ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (n + 1), g m (n - m) =
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), g i j := by sorry
