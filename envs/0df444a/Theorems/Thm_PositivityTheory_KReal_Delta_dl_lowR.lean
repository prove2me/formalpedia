-- Prove2me | Theorems.Thm_PositivityTheory_KReal_Delta_dl_lowR
-- name    : PositivityTheory.KReal.Delta.dl_lowR
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:35:12.051328+00:00
-- url     : https://prove2.me/theorems/edd44f6b-7892-5fca-9eea-f3a5bdcdf61a
-- title:
--   Delta: dl low R
-- statement:
--   The Delta construction uses the dl low R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L150-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L150-L153

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

theorem PositivityTheory.KReal.Delta.dl_lowR (a : Ix p q) (k : Fin s) (f : Pol p q r s) :
    dl p q r s (lowB (a, Sum.inr k) f) =
      (lowB ((a, Sum.inr k) : Ln p q 0 s)).lTensor _ (dl p q r s f) := by sorry
