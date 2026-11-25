-- Prove2me | Theorems.Thm_PositivityTheory_KReal_cas_bound
-- name    : PositivityTheory.KReal.cas_bound
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:51:00.68137+00:00
-- url     : https://prove2.me/theorems/f8223f7c-9c97-51ce-8a51-c9dfefe51320
-- title:
--   KReal: cas bound
-- statement:
--   The KReal construction uses the cas bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCas.lean#L12-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCas.lean#L12-L147

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasA
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasB
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasC
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal

theorem PositivityTheory.KReal.cas_bound {K I : Type} [Fintype K] [Fintype I] [DecidableEq I] (σ : K → K) (hσ : Function.Involutive σ)
    {M : Type} [AddCommGroup M] [Module ℂ M] (e : K → Module.End ℂ M) (X : I → Module.End ℂ M)
    (c : K → Matrix I I ℂ) (d c0 : ℝ)
    (h1 : ∀ k i, e k * X i - X i * e k = ∑ j, c k j i • X j)
    (h2 : ∀ i j, X i * X j - X j * X i ∈ Submodule.span ℂ (Set.range e))
    (h3 : ∀ k, c (σ k) = (c k)ᴴ)
    (h4 : ∑ k, c k * c (σ k) = (d : ℂ) • (1 : Matrix I I ℂ))
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : K → Module.End ℂ V) (hadj : ∀ k u v, ⟪ρ k u, v⟫_ℂ = ⟪u, ρ (σ k) v⟫_ℂ)
    (hc0 : ∑ k, ρ k * ρ (σ k) = (c0 : ℂ) • (1 : Module.End ℂ V))
    (ι : V →ₗ[ℂ] M) (hι : ∀ k v, ι (ρ k v) = e k (ι v))
    (h5 : ∀ t : ℝ, t ≤ c0 + d → ∀ x ∈ Submodule.span ℂ {y | ∃ i v, y = X i (ι v)},
      (∑ k, e k * e (σ k)) x = (t : ℂ) • x → x = 0)
    (G : Submodule ℂ M)
    (hG : G = sInf {N | LinearMap.range ι ≤ N ∧ (∀ k, ∀ x ∈ N, e k x ∈ N) ∧ ∀ i, ∀ x ∈ N, X i x ∈ N}) :
    (∀ x ∈ G, (∑ k, e k * e (σ k)) x - (c0 : ℂ) • x ∈ LinearMap.range ι → x ∈ LinearMap.range ι) ∧
    ∀ x ∈ G, ∃ F : Submodule ℂ M, FiniteDimensional ℂ F ∧ x ∈ F ∧ ∀ k, ∀ y ∈ F, e k y ∈ F := by sorry
