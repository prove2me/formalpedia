-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_dens_inv
-- name    : PositivityTheory.ThKG.Loc.Bump.dens_inv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:04:24.223293+00:00
-- url     : https://prove2.me/theorems/bb84d29d-4556-4931-b337-a3145cff65f6
-- title:
--   Bump: dens inv
-- statement:
--   The Bump construction uses the dens inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/DictHaar.lean#L38-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/DictHaar.lean#L38-L58

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_DictHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
variable {ι : Type} [Fintype ι]

theorem PositivityTheory.ThKG.Loc.Bump.dens_inv (s : ι → ℂ) (hs : ∀ w, s w ≠ 0) (A : Set (ι → ℂ)) (hA : MeasurableSet A) :
    volume.withDensity (fun c => (dens c : ℝ≥0∞)) ((fun c => s * c) ⁻¹' A) = volume.withDensity (fun c => (dens c : ℝ≥0∞)) A := by sorry
