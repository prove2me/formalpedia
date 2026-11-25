-- Prove2me | Theorems.Thm_PositivityTheory_KReal_Delta_derL
-- name    : PositivityTheory.KReal.Delta.derL
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:26:26.605084+00:00
-- url     : https://prove2.me/theorems/194afe67-7758-491f-9080-69abfc10bb10
-- title:
--   Delta: der L
-- statement:
--   The Delta construction uses the der L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L28-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L28-L37

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

theorem PositivityTheory.KReal.Delta.derL (D : Derivation ℂ A A) (t : A ⊗[ℂ] B) (x : A) (y : B) :
    D.toLinearMap.rTensor B (t * (x ⊗ₜ[ℂ] y)) =
      D.toLinearMap.rTensor B t * (x ⊗ₜ[ℂ] y) + t * (D x ⊗ₜ[ℂ] y) := by sorry
