-- Prove2me | Theorems.Thm_P2M_PositivityTheory_ThKG_Loc_Bump_norming__019b125911dd
-- name    : P2M_PositivityTheory_ThKG_Loc_Bump_norming__019b125911dd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:11:11.921043+00:00
-- url     : https://prove2.me/theorems/70568d11-74d9-4f6c-a870-b08f66edea20
-- title:
--   P2 M Positivity Theory Th KG Loc Bump norming  019b125911dd: P2 M Positivity Theory Th KG Loc Bump norming  019b125911dd
-- statement:
--   The P2 M Positivity Theory Th KG Loc Bump norming  019b125911dd construction uses the P2 M Positivity Theory Th KG Loc Bump norming  019b125911dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/SliceAn.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/SliceAn.lean#L40-L42

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

theorem P2M_PositivityTheory_ThKG_Loc_Bump_norming__019b125911dd (q : Seminorm ℂ S) (hq : Continuous q) (g : S) : ∃ T : S →L[ℂ] ℂ, ‖T g‖ = q g ∧ ∀ x, ‖T x‖ ≤ q x := by sorry

alias «PositivityTheory».«ThKG».«Loc».«Bump».«norming'» := P2M_PositivityTheory_ThKG_Loc_Bump_norming__019b125911dd
