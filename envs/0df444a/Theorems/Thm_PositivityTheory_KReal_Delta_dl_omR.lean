-- Prove2me | Theorems.Thm_PositivityTheory_KReal_Delta_dl_omR
-- name    : PositivityTheory.KReal.Delta.dl_omR
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:25:50.20023+00:00
-- url     : https://prove2.me/theorems/5faedda6-6c57-415a-8c4b-dce9c7fdb8c0
-- title:
--   Delta: dl om R
-- statement:
--   The Delta construction uses the dl om R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L177-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L177-L187

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

theorem PositivityTheory.KReal.Delta.dl_omR (a b : Ix p q) (k : Fin s) (f : Pol p q r s) :
    dl p q r s (omE (a, Sum.inr k) (b, Sum.inr k) f) =
      (omE ((a, Sum.inr k) : Ln p q 0 s) (b, Sum.inr k)).lTensor _ (dl p q r s f) := by sorry
