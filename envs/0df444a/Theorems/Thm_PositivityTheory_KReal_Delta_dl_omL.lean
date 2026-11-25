-- Prove2me | Theorems.Thm_PositivityTheory_KReal_Delta_dl_omL
-- name    : PositivityTheory.KReal.Delta.dl_omL
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:25:36.683808+00:00
-- url     : https://prove2.me/theorems/642eb93d-536c-4862-ac5d-66ef66325a38
-- title:
--   Delta: dl om L
-- statement:
--   The Delta construction uses the dl om L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L165-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L165-L175

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

theorem PositivityTheory.KReal.Delta.dl_omL (a b : Ix p q) (k : Fin r) (f : Pol p q r s) :
    dl p q r s (omE (a, Sum.inl k) (b, Sum.inl k) f) =
      (omE ((a, Sum.inl k) : Ln p q r 0) (b, Sum.inl k)).rTensor _ (dl p q r s f) := by sorry
