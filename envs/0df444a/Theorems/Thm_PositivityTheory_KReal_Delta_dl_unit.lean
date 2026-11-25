-- Prove2me | Theorems.Thm_PositivityTheory_KReal_Delta_dl_unit
-- name    : PositivityTheory.KReal.Delta.dl_unit
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:59.249557+00:00
-- url     : https://prove2.me/theorems/99789dc5-d739-52e2-8eaf-be6a992c2250
-- title:
--   Delta: dl unit
-- statement:
--   The Delta construction uses the dl unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L232-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L232-L238

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

theorem PositivityTheory.KReal.Delta.dl_unit (a b : Ix p q) (f : Pol p q r s) :
    dl p q r s (fockAct1 p q r s (Eab a b) f) =
      (fockAct1 p q r 0 (Eab a b)).rTensor _ (dl p q r s f) +
      (fockAct1 p q 0 s (Eab a b)).lTensor _ (dl p q r s f) := by sorry
