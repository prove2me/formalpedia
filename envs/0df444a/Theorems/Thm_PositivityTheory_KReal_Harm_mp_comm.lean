-- Prove2me | Theorems.Thm_PositivityTheory_KReal_Harm_mp_comm
-- name    : PositivityTheory.KReal.Harm.mp_comm
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:40:15.092117+00:00
-- url     : https://prove2.me/theorems/ccfb587c-006b-45cf-8451-bc0c713c70fb
-- title:
--   Harm: mp comm
-- statement:
--   The Harm construction uses the mp comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L43-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L43-L55

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

theorem PositivityTheory.KReal.Harm.mp_comm (T A B : Module.End ℂ (MvPolynomial σ ℂ))
    (hT : ∀ e P, homogeneousComponent e (T P) = T (homogeneousComponent e P))
    (h : T * A - A * T = B) (g : MvPolynomial σ ℂ) :
    T (minusPart A g) - minusPart A (T g) = minusPart B g := by sorry
