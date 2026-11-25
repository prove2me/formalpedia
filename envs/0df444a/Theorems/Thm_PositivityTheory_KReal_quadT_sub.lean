-- Prove2me | Theorems.Thm_PositivityTheory_KReal_quadT_sub
-- name    : PositivityTheory.KReal.quadT_sub
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:32:50.792902+00:00
-- url     : https://prove2.me/theorems/e0f9ae8c-5fb5-452f-820e-9bf987c1f7fc
-- title:
--   KReal: quad T sub
-- statement:
--   The KReal construction uses the quad T sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreLie.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreLie.lean#L12-L15

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

theorem PositivityTheory.KReal.quadT_sub {ι E : Type*} [Fintype ι] [Ring E] [Algebra ℂ E] (R L : ι → E) (A B : Matrix ι ι ℂ) :
    quadT R L (A - B) = quadT R L A - quadT R L B := by sorry
