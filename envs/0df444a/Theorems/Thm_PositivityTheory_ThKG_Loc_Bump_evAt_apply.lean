-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_evAt_apply
-- name    : PositivityTheory.ThKG.Loc.Bump.evAt_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:00:44.284073+00:00
-- url     : https://prove2.me/theorems/f007827b-de82-40e4-b061-85aa246ab438
-- title:
--   Bump: ev At apply
-- statement:
--   The Bump construction uses the ev At apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/SliceAn.lean#L172-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/SliceAn.lean#L172-L172

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

theorem PositivityTheory.ThKG.Loc.Bump.evAt_apply (x : V) (f : 𝓢(V, ℂ)) : evAt x f = f x := by sorry
