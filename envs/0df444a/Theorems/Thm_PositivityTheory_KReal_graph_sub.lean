-- Prove2me | Theorems.Thm_PositivityTheory_KReal_graph_sub
-- name    : PositivityTheory.KReal.graph_sub
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:31:41.716443+00:00
-- url     : https://prove2.me/theorems/ae8add17-b60f-4c57-bfd8-55c60d55b9e2
-- title:
--   KReal: graph sub
-- statement:
--   The KReal construction uses the graph sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreGraph.lean#L39-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreGraph.lean#L39-L226

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

theorem PositivityTheory.KReal.graph_sub {p q : ℕ} {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    (ρA : Mat p q →ₗ[ℂ] Module.End ℂ A) (ρB : Mat p q →ₗ[ℂ] Module.End ℂ B)
    (hA : IsLie ρA) (hB : IsLie ρB) (aA : AdjG ρA) (aB : AdjG ρB) (lam : Ix p q → ℂ) (x : A) (y : B)
    (hx0 : x ≠ 0)
    (hxK : ∀ a b, sameBlock a b → ρA (Eab a b) x = (if a = b then lam a else 0) • x)
    (hyK : ∀ a b, sameBlock a b → ρB (Eab a b) y = (if a = b then lam a else 0) • y)
    (hxP : ∀ i j, ρA (Eab (.inr j) (.inl i)) x = 0) (hyP : ∀ i j, ρB (Eab (.inr j) (.inl i)) y = 0) :
    ∃ N : Submodule ℂ (A × B), (x, y) ∈ N ∧ (∀ W, ∀ n ∈ N, prodAct ρA ρB W n ∈ N) ∧
      ∀ v, ((0 : A), v) ∈ N → v = 0 := by sorry
