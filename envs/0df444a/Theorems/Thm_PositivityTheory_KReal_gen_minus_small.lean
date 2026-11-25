-- Prove2me | Theorems.Thm_PositivityTheory_KReal_gen_minus_small
-- name    : PositivityTheory.KReal.gen_minus_small
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:49:42.497812+00:00
-- url     : https://prove2.me/theorems/a4f2f894-308d-59dd-8564-e681d83cfd0a
-- title:
--   KReal: gen minus small
-- statement:
--   The KReal construction uses the gen minus small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreGen.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreGen.lean#L12-L19

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

theorem PositivityTheory.KReal.gen_minus_small {σ : Type} (A : Module.End ℂ (MvPolynomial σ ℂ)) {d : ℕ} (hd : d < 2)
    {g : MvPolynomial σ ℂ} (hg : g ∈ homog σ d) : minusPart A g = 0 := by sorry
