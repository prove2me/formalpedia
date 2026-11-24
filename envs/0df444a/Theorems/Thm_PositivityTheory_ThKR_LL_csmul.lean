-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_LL_csmul
-- name    : PositivityTheory.ThKR.LL.csmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:26:10.764043+00:00
-- url     : https://prove2.me/theorems/2d2bf7fd-d353-449d-903b-25529d439e06
-- title:
--   LL: csmul
-- statement:
--   The LL construction uses the csmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/HasDerivAtSchwartzToL2.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/HasDerivAtSchwartzToL2.lean#L18-L20

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaDef
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
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

theorem PositivityTheory.ThKR.LL.csmul (r : ℝ) (x : L2 l) : (r : ℂ) • x = r • x := by sorry
