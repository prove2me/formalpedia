-- Prove2me | Theorems.Thm_PositivityTheory_KReal_Delta_derR
-- name    : PositivityTheory.KReal.Delta.derR
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:24:16.662831+00:00
-- url     : https://prove2.me/theorems/18a0441a-e2ce-4400-a26d-c4853503ad34
-- title:
--   Delta: der R
-- statement:
--   The Delta construction uses the der R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L39-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L39-L48

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

theorem PositivityTheory.KReal.Delta.derR (D : Derivation ℂ B B) (t : A ⊗[ℂ] B) (x : A) (y : B) :
    D.toLinearMap.lTensor A (t * (x ⊗ₜ[ℂ] y)) =
      D.toLinearMap.lTensor A t * (x ⊗ₜ[ℂ] y) + t * (x ⊗ₜ[ℂ] D y) := by sorry
