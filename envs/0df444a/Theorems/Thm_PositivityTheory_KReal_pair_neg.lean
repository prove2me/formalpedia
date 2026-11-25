-- Prove2me | Theorems.Thm_PositivityTheory_KReal_pair_neg
-- name    : PositivityTheory.KReal.pair_neg
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:46:44.123485+00:00
-- url     : https://prove2.me/theorems/b3a7a334-43c8-5271-8d9f-009a3aaf2624
-- title:
--   KReal: pair neg
-- statement:
--   The KReal construction uses the pair neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CorePair.lean#L115-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CorePair.lean#L115-L127

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CorePair
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

theorem PositivityTheory.KReal.pair_neg {p q r s n m : ℕ} (hq : q ≤ r) (hp : p ≤ s) (hn : 0 < n) (hm : 0 < m) (c0 : ℚ)
    (h1 : c0 = -m + cPair r s) (h2 : c0 = -n - cPair r s) : PairData p q r s (c0 : ℂ) := by sorry
