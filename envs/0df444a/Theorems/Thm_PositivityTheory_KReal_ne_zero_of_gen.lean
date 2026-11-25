-- Prove2me | Theorems.Thm_PositivityTheory_KReal_ne_zero_of_gen
-- name    : PositivityTheory.KReal.ne_zero_of_gen
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:03:32.457953+00:00
-- url     : https://prove2.me/theorems/2944db56-0f31-58a3-b21d-feabed3ee10a
-- title:
--   KReal: ne zero of gen
-- statement:
--   The KReal construction uses the ne zero of gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreMain.lean#L573-L581
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreMain.lean#L573-L581

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasGl
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain
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

theorem PositivityTheory.KReal.ne_zero_of_gen {r s : ℕ} {T : Type} [AddCommGroup T] [Module ℂ T] [Nontrivial T]
    (act : Mat r s →ₗ[ℂ] Module.End ℂ T) (v : T) (h : genG act (Submodule.span ℂ {v}) = ⊤) : v ≠ 0 := by sorry
