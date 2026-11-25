-- Prove2me | Theorems.Thm_PositivityTheory_KReal_prodAct_apply
-- name    : PositivityTheory.KReal.prodAct_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:33:06.918333+00:00
-- url     : https://prove2.me/theorems/3bfb3ff3-35c7-401b-8c57-32104bf69f19
-- title:
--   KReal: prod Act apply
-- statement:
--   The KReal construction uses the prod Act apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreGraph.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreGraph.lean#L35-L37

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreGraph
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

theorem PositivityTheory.KReal.prodAct_apply {p q : ℕ} {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (ρA : Mat p q →ₗ[ℂ] Module.End ℂ A) (ρB : Mat p q →ₗ[ℂ] Module.End ℂ B) (Z : Mat p q) (n : A × B) :
    prodAct ρA ρB Z n = (ρA Z n.1, ρB Z n.2) := by sorry
