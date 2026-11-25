-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_contDiff_dm
-- name    : PositivityTheory.ThKR.Mp.contDiff_dm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:38:23.132691+00:00
-- url     : https://prove2.me/theorems/f5eca3f2-e330-5c87-9ba7-6dd7a990e281
-- title:
--   Mp: cont Diff dm
-- statement:
--   The Mp construction uses the cont Diff dm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/HasFDerivAtOrb.lean#L70-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/HasFDerivAtOrb.lean#L70-L85

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MpFOne
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_HasFDerivAtOrb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL
open scoped Real ContDiff
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]

theorem PositivityTheory.ThKR.Mp.contDiff_dm {k : ℕ} (γ : (Fin k → ℝ) → G l)
    (hs : ∀ a b, ContDiff ℝ ∞ fun t => (pr (γ t) : Mat l) a b) (a b : l ⊕ l) (n : ℕ) :
    ContDiff ℝ n fun t => dm γ t a b := by sorry
