-- Prove2me | Theorems.Thm_PositivityTheory_KReal_Delta_mulR
-- name    : PositivityTheory.KReal.Delta.mulR
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:25:54.088595+00:00
-- url     : https://prove2.me/theorems/f4e8ac0b-fedc-427f-9021-9260b399600d
-- title:
--   Delta: mul R
-- statement:
--   The Delta construction uses the mul R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L22-L26

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDelta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace TensorProduct
open PositivityTheory PositivityTheory.KReal
open PositivityTheory.KReal.Delta
variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]

theorem PositivityTheory.KReal.Delta.mulR (y : B) (t : A ⊗[ℂ] B) : ((1 : A) ⊗ₜ[ℂ] y) * t = (LinearMap.mulLeft ℂ y).lTensor A t := by sorry
