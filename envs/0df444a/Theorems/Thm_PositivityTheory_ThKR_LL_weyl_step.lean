-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_LL_weyl_step
-- name    : PositivityTheory.ThKR.LL.weyl_step
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:17:03.121905+00:00
-- url     : https://prove2.me/theorems/ffeca83f-8e89-5800-9d64-4158bd853ac1
-- title:
--   LL: weyl step
-- statement:
--   The LL construction uses the weyl step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/HasDerivAtSchwartzToL2.lean#L102-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/HasDerivAtSchwartzToL2.lean#L102-L107

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaDef
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Theorems.Thm_PositivityTheory_ThKF_E_Impl_dRho

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
open scoped Real
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l]
variable [DecidableEq l]

theorem PositivityTheory.ThKR.LL.weyl_step {V : Sch l →L[ℂ] Sch l} {w v : l ⊕ l → ℝ} (h : ∀ f, dRho w (V f) = V (dRho v f))
    (A : Sch l →L[ℂ] Sch l) (f : Sch l) :
    schwartzToL2 l ((A * dRho w) (V f)) = ∑ a, v a • schwartzToL2 l (A (V (dRho (Pi.single a 1) f))) := by sorry
