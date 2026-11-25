-- Prove2me | Theorems.Thm_PositivityTheory_KReal_Delta_sumR
-- name    : PositivityTheory.KReal.Delta.sumR
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:33:04.400651+00:00
-- url     : https://prove2.me/theorems/130f8dfd-539d-4c91-829c-ebe819c6cd8d
-- title:
--   Delta: sum R
-- statement:
--   The Delta construction uses the sum R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L220-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L220-L228

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
variable {p q r s : ℕ}
variable (b : Pol p q r 0 →ₗ[ℂ] Pol p q 0 s →ₗ[ℂ] ℂ)

theorem PositivityTheory.KReal.Delta.sumR {ι : Type} [Fintype ι] (F : ι → Module.End ℂ (Pol p q 0 s)) (t : Pol p q r 0 ⊗[ℂ] Pol p q 0 s) :
    (∑ i, F i).lTensor (Pol p q r 0) t = ∑ i, (F i).lTensor (Pol p q r 0) t := by sorry
