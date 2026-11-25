-- Prove2me | Theorems.Thm_PositivityTheory_KReal_pad_l
-- name    : PositivityTheory.KReal.pad_l
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:41:24.128322+00:00
-- url     : https://prove2.me/theorems/e4ec3b3d-4859-43e0-b5f3-e0e0e53f5e5c
-- title:
--   KReal: pad l
-- statement:
--   The KReal construction uses the pad l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CorePair.lean#L85-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CorePair.lean#L85-L87

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

theorem PositivityTheory.KReal.pad_l (k : ℕ) (z : ℤ) (i : Fin k) :
    (pad (List.replicate k z) (k - (List.replicate k z).length - ([] : List ℤ).length) []).getD i 0 = (z : ℚ) := by sorry
