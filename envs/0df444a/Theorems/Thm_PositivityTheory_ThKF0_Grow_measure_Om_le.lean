-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Grow_measure_Om_le
-- name    : PositivityTheory.ThKF0.Grow.measure_Om_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:04:00.790243+00:00
-- url     : https://prove2.me/theorems/ac0467b9-0e8b-521a-b843-a3ad2f4aa2a0
-- title:
--   Grow: measure Om le
-- statement:
--   The Grow construction uses the measure Om le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/GrowSobB.lean#L38-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/GrowSobB.lean#L38-L52

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_GrowSobB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Grow
open scoped ENNReal Classical
open NumberField IsDedekindDomain MeasureTheory
variable (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]

theorem PositivityTheory.ThKF0.Grow.measure_Om_le [MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F)] [BorelSpace (κ → FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (κ → FiniteAdeleRing (𝓞 F) F)) [ν.IsAddRightInvariant] :
    ∃ k : ℕ, ∀ m : ℕ, 1 ≤ m → ν (Om F κ) ≤ (m : ℝ≥0∞) ^ k * ν ((fun u => m • u) '' Om F κ) := by sorry
