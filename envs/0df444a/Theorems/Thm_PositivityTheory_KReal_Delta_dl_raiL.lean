-- Prove2me | Theorems.Thm_PositivityTheory_KReal_Delta_dl_raiL
-- name    : PositivityTheory.KReal.Delta.dl_raiL
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:23:42.796805+00:00
-- url     : https://prove2.me/theorems/1d82d0dd-eb72-438f-882f-3c730cf54ff3
-- title:
--   Delta: dl rai L
-- statement:
--   The Delta construction uses the dl rai L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L155-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L155-L158

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

theorem PositivityTheory.KReal.Delta.dl_raiL (a : Ix p q) (k : Fin r) (f : Pol p q r s) :
    dl p q r s (raiB (a, Sum.inl k) f) =
      (raiB ((a, Sum.inl k) : Ln p q r 0)).rTensor _ (dl p q r s f) := by sorry
