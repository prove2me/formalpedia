-- Prove2me | Theorems.Thm_PositivityTheory_KReal_Harm_mp_sub
-- name    : PositivityTheory.KReal.Harm.mp_sub
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:50:13.272898+00:00
-- url     : https://prove2.me/theorems/3ac8d2ce-15d4-5395-aa8e-62f141ce67f0
-- title:
--   Harm: mp sub
-- statement:
--   The Harm construction uses the mp sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L57-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L57-L61

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

theorem PositivityTheory.KReal.Harm.mp_sub (A B : Module.End ℂ (MvPolynomial σ ℂ)) (g : MvPolynomial σ ℂ) :
    minusPart (A - B) g = minusPart A g - minusPart B g := by sorry
