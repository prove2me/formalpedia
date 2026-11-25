-- Prove2me | Theorems.Thm_PositivityTheory_KReal_Harm_mp_add_right
-- name    : PositivityTheory.KReal.Harm.mp_add_right
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:57:33.298362+00:00
-- url     : https://prove2.me/theorems/114038ad-8950-569b-ac09-2b76e5d3edc5
-- title:
--   Harm: mp add right
-- statement:
--   The Harm construction uses the mp add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L68-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L68-L71

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

theorem PositivityTheory.KReal.Harm.mp_add_right (A : Module.End ℂ (MvPolynomial σ ℂ)) (g g' : MvPolynomial σ ℂ) :
    minusPart A (g + g') = minusPart A g + minusPart A g' := by sorry
