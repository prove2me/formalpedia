-- Prove2me | Theorems.Thm_PositivityTheory_KReal_omAct_lie
-- name    : PositivityTheory.KReal.omAct_lie
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:30:25.01508+00:00
-- url     : https://prove2.me/theorems/8991cc96-9219-5a24-a9a0-5201dc25bec6
-- title:
--   KReal: om Act lie
-- statement:
--   The KReal construction uses the om Act lie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreLie.lean#L17-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreLie.lean#L17-L29

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
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
variable {p q r s : ℕ}

theorem PositivityTheory.KReal.omAct_lie (M N : Matrix (Ln p q r s) (Ln p q r s) ℂ) :
    omAct p q r s M * omAct p q r s N - omAct p q r s N * omAct p q r s M = omAct p q r s (M * N - N * M) := by sorry
