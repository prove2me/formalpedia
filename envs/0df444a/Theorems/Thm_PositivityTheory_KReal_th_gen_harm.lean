-- Prove2me | Theorems.Thm_PositivityTheory_KReal_th_gen_harm
-- name    : PositivityTheory.KReal.th_gen_harm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:59:30.453125+00:00
-- url     : https://prove2.me/theorems/6b3c7450-3d86-530f-8197-ff46ac96e475
-- title:
--   KReal: th gen harm
-- statement:
--   The KReal construction uses the th gen harm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreGen.lean#L21-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreGen.lean#L21-L75

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreSplit
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreGen
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

theorem PositivityTheory.KReal.th_gen_harm (c τ : ℂ) (c0 : ℚ) (hc : c = c0) (N : Submodule ℂ (ThC p q r s c))
    (hH : (jHarm p q r s ⊓ polChi p q r s c).map (thMkC p q r s c) ≤ N)
    (hN : ∀ W, ∀ x ∈ N, thAct p q r s c τ W x ∈ N) : N = ⊤ := by sorry
