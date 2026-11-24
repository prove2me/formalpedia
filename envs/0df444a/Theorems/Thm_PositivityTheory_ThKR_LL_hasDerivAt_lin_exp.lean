-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_LL_hasDerivAt_lin_exp
-- name    : PositivityTheory.ThKR.LL.hasDerivAt_lin_exp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:17.445812+00:00
-- url     : https://prove2.me/theorems/143cb6d4-9436-4ada-82ea-0b39c5261d4c
-- title:
--   LL: has Deriv At lin exp
-- statement:
--   The LL construction uses the has Deriv At lin exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalLift.lean#L45-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalLift.lean#L45-L50

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_NormExpSubLe
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l] [DecidableEq l]

theorem PositivityTheory.ThKR.LL.hasDerivAt_lin_exp {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Matrix (l ⊕ l) (l ⊕ l) ℝ →ₗ[ℝ] F)
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => L (NormedSpace.exp (t • X))) (L (NormedSpace.exp (t • X) * X)) t := by sorry
