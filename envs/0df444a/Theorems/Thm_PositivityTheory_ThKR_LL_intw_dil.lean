-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_LL_intw_dil
-- name    : PositivityTheory.ThKR.LL.intw_dil
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:07:09.843168+00:00
-- url     : https://prove2.me/theorems/cac10a32-48fc-57e4-8ced-e887ab165b51
-- title:
--   LL: intw dil
-- statement:
--   The LL construction uses the intw dil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/IsoOfIntegral.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/IsoOfIntegral.lean#L111-L114

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
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

theorem PositivityTheory.ThKR.LL.intw_dil {B : Eu l →L[ℝ] Eu l} (hB : IsUnit B) {p q p' q' : Eu l} (hp : B p' = p) (hq : ∀ x, ⟪q', x⟫ = ⟪q, B x⟫) :
    Intw (dil B) p q p' q' := by sorry
