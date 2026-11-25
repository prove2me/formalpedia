-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_LL_fou_mq_fouInv
-- name    : PositivityTheory.ThKR.LL.fou_mq_fouInv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:36.740992+00:00
-- url     : https://prove2.me/theorems/ea37eccf-6459-44c3-9d88-9cc9bf30468a
-- title:
--   LL: fou mq fou Inv
-- statement:
--   The LL construction uses the fou mq fou Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalLift.lean#L89-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalLift.lean#L89-L111

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

theorem PositivityTheory.ThKR.LL.fou_mq_fouInv (B : Matrix l l ℝ) (f : Sch l) :
    fou l (mq (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) B)) (fouInv l f)) =
      (4 * π * I : ℂ)⁻¹ • ∑ j, ∑ k, (B j k : ℂ) • (∂_{(EuclideanSpace.single j 1 : Eu l)}
        (∂_{(EuclideanSpace.single k 1 : Eu l)} f)) := by sorry
