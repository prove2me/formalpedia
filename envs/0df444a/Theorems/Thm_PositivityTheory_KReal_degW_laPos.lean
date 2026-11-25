-- Prove2me | Theorems.Thm_PositivityTheory_KReal_degW_laPos
-- name    : PositivityTheory.KReal.degW_laPos
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:23:17.38728+00:00
-- url     : https://prove2.me/theorems/f2a8d7fc-f0e4-5b58-8ba9-f3760fddb569
-- title:
--   KReal: deg W la Pos
-- statement:
--   The KReal construction uses the deg W la Pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasW.lean#L113-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasW.lean#L113-L122

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasW
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
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal

theorem PositivityTheory.KReal.degW_laPos {p q r s n m : ℕ} (hp : p ≤ r) (hq : q ≤ s) :
    degW (cPair p q) (laPos p q r s n m) = p * n + q * m := by sorry
