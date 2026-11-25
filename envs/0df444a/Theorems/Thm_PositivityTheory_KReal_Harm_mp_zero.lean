-- Prove2me | Theorems.Thm_PositivityTheory_KReal_Harm_mp_zero
-- name    : PositivityTheory.KReal.Harm.mp_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:37:46.641116+00:00
-- url     : https://prove2.me/theorems/c53c68da-cf22-54f9-acd0-0dc2225ff4e2
-- title:
--   Harm: mp zero
-- statement:
--   The Harm construction uses the mp zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L63-L66

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreHarm
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
open PositivityTheory.KReal.Harm
variable {σ : Type}

theorem PositivityTheory.KReal.Harm.mp_zero (g : MvPolynomial σ ℂ) : minusPart (0 : Module.End ℂ (MvPolynomial σ ℂ)) g = 0 := by sorry
