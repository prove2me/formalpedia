-- Prove2me | Theorems.Thm_PositivityTheory_KReal_graph_orth_stable
-- name    : PositivityTheory.KReal.graph_orth_stable
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:45:11.474117+00:00
-- url     : https://prove2.me/theorems/7f5e8223-b84a-4fb0-aa20-86f4eb39de8c
-- title:
--   KReal: graph orth stable
-- statement:
--   The KReal construction uses the graph orth stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreGraph.lean#L10-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreGraph.lean#L10-L22

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

theorem PositivityTheory.KReal.graph_orth_stable {p q : ℕ} {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    (ρ : Mat p q →ₗ[ℂ] Module.End ℂ A) (aA : AdjG ρ) (K : Submodule ℂ A) (hK : ∀ W, ∀ v ∈ K, ρ W v ∈ K) :
    ∀ W, ∀ u ∈ Kᗮ, ρ W u ∈ Kᗮ := by sorry
