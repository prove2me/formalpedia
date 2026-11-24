-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_norming
-- name    : PositivityTheory.ThKG.Loc.Bump.norming
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:53.019422+00:00
-- url     : https://prove2.me/theorems/a705765e-69a5-48d3-9406-a5de4eeaa226
-- title:
--   Bump: norming
-- statement:
--   The Bump construction uses the norming property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/SliceAn.lean#L15-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/SliceAn.lean#L15-L29

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedFDerivSubApply
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_SliceAn
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
open scoped SchwartzMap NNReal
variable {S : Type} [AddCommGroup S] [Module ℂ S]

theorem PositivityTheory.ThKG.Loc.Bump.norming (q : Seminorm ℂ S) (g : S) : ∃ T : S →ₗ[ℂ] ℂ, ‖T g‖ = q g ∧ ∀ x, ‖T x‖ ≤ q x := by sorry
