-- Prove2me | Theorems.Thm_PositivityTheory_KReal_Delta_dl_lowL
-- name    : PositivityTheory.KReal.Delta.dl_lowL
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:26.917791+00:00
-- url     : https://prove2.me/theorems/ecc881a7-7dbf-4bd6-bd77-9f4c91bcc765
-- title:
--   Delta: dl low L
-- statement:
--   The Delta construction uses the dl low L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L145-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L145-L148

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

theorem PositivityTheory.KReal.Delta.dl_lowL (a : Ix p q) (k : Fin r) (f : Pol p q r s) :
    dl p q r s (lowB (a, Sum.inl k) f) =
      (lowB ((a, Sum.inl k) : Ln p q r 0)).rTensor _ (dl p q r s f) := by sorry
