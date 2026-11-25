-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_eq_of_weak
-- name    : PositivityTheory.ThKG.Loc.Bump.eq_of_weak
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:04:22.592547+00:00
-- url     : https://prove2.me/theorems/25bf9d9d-4b90-5d37-a8cb-dd1325a2249b
-- title:
--   Bump: eq of weak
-- statement:
--   The Bump construction uses the eq of weak property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/SliceAn.lean#L174-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/SliceAn.lean#L174-L175

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
variable {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]

theorem PositivityTheory.ThKG.Loc.Bump.eq_of_weak {f g : 𝓢(V, ℂ)} (h : ∀ T : 𝓢(V, ℂ) →L[ℂ] ℂ, T f = T g) : f = g := by sorry
