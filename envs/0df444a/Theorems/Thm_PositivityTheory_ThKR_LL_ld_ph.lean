-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_LL_ld_ph
-- name    : PositivityTheory.ThKR.LL.ld_ph
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:07:18.964272+00:00
-- url     : https://prove2.me/theorems/24a6c7e2-7c89-5028-8102-16ee0bcaf49b
-- title:
--   LL: ld ph
-- statement:
--   The LL construction uses the ld ph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/NormExpSubLe.lean#L36-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/NormExpSubLe.lean#L36-L63

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_NormExpSubLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l]

theorem PositivityTheory.ThKR.LL.ld_ph {S : ℝ → Eu l →L[ℝ] Eu l} {S' : Eu l →L[ℝ] Eu l} {t₀ : ℝ} (h : HasDerivAt S S' t₀) :
    LD (fun t => ph (S t)) (fun f => mq S' (ph (S t₀) f)) t₀ := by sorry
