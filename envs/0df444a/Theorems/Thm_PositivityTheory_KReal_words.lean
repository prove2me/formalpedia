-- Prove2me | Theorems.Thm_PositivityTheory_KReal_words
-- name    : PositivityTheory.KReal.words
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:24:47.652594+00:00
-- url     : https://prove2.me/theorems/95f677ef-1cc6-5e8b-83de-11531f974a0b
-- title:
--   KReal: words
-- statement:
--   The KReal construction uses the words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCyc.lean#L10-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCyc.lean#L10-L62

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
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

theorem PositivityTheory.KReal.words {M : Type} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ (Module.End ℂ M))
    (hS : ∀ E ∈ S, ∀ F ∈ S, E * F - F * E ∈ S) (L : Set (Module.End ℂ M)) (hL : L ⊆ S) (z : M)
    (hz : ∀ E ∈ S, ∃ F ∈ Submodule.span ℂ L, ∃ c : ℂ, E z = F z + c • z)
    (W : Submodule ℂ M) (hW : W = sInf {N | z ∈ N ∧ ∀ F ∈ L, ∀ x ∈ N, F x ∈ N}) :
    z ∈ W ∧ (∀ E ∈ S, ∀ x ∈ W, E x ∈ W) ∧ W = Submodule.span ℂ {z} ⊔ ⨆ F ∈ L, W.map F := by sorry
