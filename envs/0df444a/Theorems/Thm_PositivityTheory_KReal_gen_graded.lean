-- Prove2me | Theorems.Thm_PositivityTheory_KReal_gen_graded
-- name    : PositivityTheory.KReal.gen_graded
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:36:52.229332+00:00
-- url     : https://prove2.me/theorems/30f662ab-d0bb-5d20-a76e-21d261cd2858
-- title:
--   KReal: gen graded
-- statement:
--   The KReal construction uses the gen graded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreProj.lean#L49-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreProj.lean#L49-L83

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreProj
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

theorem PositivityTheory.KReal.gen_graded {p q r : ℕ} (x : Pol p q r 0) (dx : ℕ) (hx : x ∈ homog (Ix p q × Ix r 0) dx) :
    ∀ d, ∀ z ∈ genG (fockAct1 p q r 0) (Submodule.span ℂ {x}),
      homogeneousComponent d z ∈ genG (fockAct1 p q r 0) (Submodule.span ℂ {x}) := by sorry
