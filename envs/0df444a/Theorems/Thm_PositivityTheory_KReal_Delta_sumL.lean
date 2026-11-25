-- Prove2me | Theorems.Thm_PositivityTheory_KReal_Delta_sumL
-- name    : PositivityTheory.KReal.Delta.sumL
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:30:38.853279+00:00
-- url     : https://prove2.me/theorems/db6515c4-412a-4cc5-be6a-e125c0c243c1
-- title:
--   Delta: sum L
-- statement:
--   The Delta construction uses the sum L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L210-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L210-L218

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

theorem PositivityTheory.KReal.Delta.sumL {ι : Type} [Fintype ι] (F : ι → Module.End ℂ (Pol p q r 0)) (t : Pol p q r 0 ⊗[ℂ] Pol p q 0 s) :
    (∑ i, F i).rTensor (Pol p q 0 s) t = ∑ i, (F i).rTensor (Pol p q 0 s) t := by sorry
