-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_weak_bounded
-- name    : PositivityTheory.ThKG.Loc.Bump.weak_bounded
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:01:05.653742+00:00
-- url     : https://prove2.me/theorems/ebbb16f7-21e4-4fec-a6ad-9cb3cf784c87
-- title:
--   Bump: weak bounded
-- statement:
--   The Bump construction uses the weak bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/SliceAn.lean#L52-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/SliceAn.lean#L52-L64

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
variable [TopologicalSpace S] [IsTopologicalAddGroup S]

theorem PositivityTheory.ThKG.Loc.Bump.weak_bounded {ι : Type} (g : ι → S) (h : ∀ T : S →L[ℂ] ℂ, ∃ C, ∀ i, ‖T (g i)‖ ≤ C) (q : Seminorm ℂ S) (hq : Continuous q) :
    ∃ C, ∀ i, q (g i) ≤ C := by sorry
