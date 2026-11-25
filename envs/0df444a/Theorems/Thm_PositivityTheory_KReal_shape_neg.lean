-- Prove2me | Theorems.Thm_PositivityTheory_KReal_shape_neg
-- name    : PositivityTheory.KReal.shape_neg
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:22:12.218627+00:00
-- url     : https://prove2.me/theorems/fb61509a-668a-5517-a996-31d202a27d86
-- title:
--   KReal: shape neg
-- statement:
--   The KReal construction uses the shape neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreShape.lean#L144-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreShape.lean#L144-L190

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreShape
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

theorem PositivityTheory.KReal.shape_neg {p q r s n m : ℕ} (hq : q ≤ r) (hp : p ≤ s) (hn : 0 < n) (hm : 0 < m) (c0 : ℚ)
    (h1 : c0 = -m + cPair r s) (h2 : c0 = -n - cPair r s) :
    JointShape p q r s (fun _ => c0) (laNeg p q r s n m) ∧
      ∀ ν, JointShape p q r s (fun _ => c0) ν → ν = laNeg p q r s n m := by sorry
