-- Prove2me | Theorems.Thm_PositivityTheory_KReal_dualAct_adj
-- name    : PositivityTheory.KReal.dualAct_adj
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:46:43.606845+00:00
-- url     : https://prove2.me/theorems/272ed934-f99d-4876-8664-f9597f0cfb29
-- title:
--   KReal: dual Act adj
-- statement:
--   The KReal construction uses the dual Act adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreNonv.lean#L84-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreNonv.lean#L84-L91

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreGraph
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDelta
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreProj
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreNonv
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
variable {p q : ℕ}

theorem PositivityTheory.KReal.dualAct_adj {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    {ρ : Mat p q →ₗ[ℂ] Module.End ℂ B} (h : AdjG ρ) (c0 : ℚ) : AdjG (dualAct ρ (c0 : ℂ)) := by sorry
