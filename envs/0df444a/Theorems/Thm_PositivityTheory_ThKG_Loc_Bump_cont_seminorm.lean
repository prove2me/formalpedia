-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_cont_seminorm
-- name    : PositivityTheory.ThKG.Loc.Bump.cont_seminorm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:47.551465+00:00
-- url     : https://prove2.me/theorems/bc89ab58-9014-4eb3-aca9-376b8475835e
-- title:
--   Bump: cont seminorm
-- statement:
--   The Bump construction uses the cont seminorm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/SliceAn.lean#L83-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/SliceAn.lean#L83-L84

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

theorem PositivityTheory.ThKG.Loc.Bump.cont_seminorm (k n : ℕ) : Continuous (SchwartzMap.seminorm ℂ k n : 𝓢(V, ℂ) → ℝ) := by sorry
