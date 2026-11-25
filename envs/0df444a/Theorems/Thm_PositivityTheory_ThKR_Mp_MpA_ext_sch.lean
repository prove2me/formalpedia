-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_MpA_ext_sch
-- name    : PositivityTheory.ThKR.Mp.MpA.ext_sch
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:30:20.845246+00:00
-- url     : https://prove2.me/theorems/9957ad72-547a-5a38-b4bc-6a9bce21b2e0
-- title:
--   Mp A: ext sch
-- statement:
--   The Mp A construction uses the ext sch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/ContinuousTo.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/ContinuousTo.lean#L22-L24

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousTo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL LineDeriv
open scoped Real ContDiff
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open PositivityTheory.ThKR.Mp.MpA

theorem PositivityTheory.ThKR.Mp.MpA.ext_sch (V : (Sch l →L[ℂ] Sch l)ˣ) (hn : ∀ f, ‖schwartzToL2 l (V.1 f)‖ = ‖schwartzToL2 l f‖) (f : Sch l) :
    ext V hn (schwartzToL2 l f) = schwartzToL2 l (V.1 f) := by sorry
