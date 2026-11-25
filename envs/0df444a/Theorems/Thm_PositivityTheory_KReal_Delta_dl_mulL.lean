-- Prove2me | Theorems.Thm_PositivityTheory_KReal_Delta_dl_mulL
-- name    : PositivityTheory.KReal.Delta.dl_mulL
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:21:50.135541+00:00
-- url     : https://prove2.me/theorems/8467bae7-1f70-53ac-a14f-2009d19fd9a5
-- title:
--   Delta: dl mul L
-- statement:
--   The Delta construction uses the dl mul L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L71-L74

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

theorem PositivityTheory.KReal.Delta.dl_mulL (a : Ix p q) (k : Fin r) (f : Pol p q r s) :
    dl p q r s (X (a, Sum.inl k) * f) =
      (LinearMap.mulLeft ℂ (X (a, Sum.inl k) : Pol p q r 0)).rTensor _ (dl p q r s f) := by sorry
