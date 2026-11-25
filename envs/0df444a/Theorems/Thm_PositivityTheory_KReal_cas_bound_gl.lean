-- Prove2me | Theorems.Thm_PositivityTheory_KReal_cas_bound_gl
-- name    : PositivityTheory.KReal.cas_bound_gl
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:53:05.189041+00:00
-- url     : https://prove2.me/theorems/06061ee3-1cd7-4cd8-83c9-725dd85c6963
-- title:
--   KReal: cas bound gl
-- statement:
--   The KReal construction uses the cas bound gl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasGl.lean#L158-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasGl.lean#L158-L228

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCas
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasGl
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
open CasGl

theorem PositivityTheory.KReal.cas_bound_gl {r s : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] (act : Mat r s →ₗ[ℂ] Module.End ℂ M)
    (hL : IsLie act) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Ix r s → Ix r s → Module.End ℂ V) (hadj : AdjK ρ) (c0 : ℝ)
    (hc0 : casK ρ = (c0 : ℂ) • (1 : Module.End ℂ V)) (ι : V →ₗ[ℂ] M)
    (hι : ∀ a b, sameBlock a b → ∀ v, ι (ρ a b v) = act (Eab a b) (ι v))
    (h5 : StarK act (LinearMap.range ι) c0) :
    (∀ x ∈ genG act (LinearMap.range ι),
      casK (units act) x - (c0 : ℂ) • x ∈ LinearMap.range ι → x ∈ LinearMap.range ι) ∧
    ∀ x ∈ genG act (LinearMap.range ι), ∃ F : Submodule ℂ M, FiniteDimensional ℂ F ∧ x ∈ F ∧ KSt (units act) F := by sorry
