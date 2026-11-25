-- Prove2me | Theorems.Thm_PositivityTheory_KReal_Delta_dl_act
-- name    : PositivityTheory.KReal.Delta.dl_act
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:31:11.713368+00:00
-- url     : https://prove2.me/theorems/9e7856a4-ff6a-4ec6-8430-0ce05282ed54
-- title:
--   Delta: dl act
-- statement:
--   The Delta construction uses the dl act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L246-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L246-L251

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

theorem PositivityTheory.KReal.Delta.dl_act (Z : Mat p q) (f : Pol p q r s) :
    dl p q r s (fockAct1 p q r s Z f) =
      (fockAct1 p q r 0 Z).rTensor _ (dl p q r s f) + (fockAct1 p q 0 s Z).lTensor _ (dl p q r s f) := by sorry
