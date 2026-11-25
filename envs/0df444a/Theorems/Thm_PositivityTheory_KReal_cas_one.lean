-- Prove2me | Theorems.Thm_PositivityTheory_KReal_cas_one
-- name    : PositivityTheory.KReal.cas_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:51:13.776837+00:00
-- url     : https://prove2.me/theorems/5e1889f2-b083-4509-8acf-332b9a12fc22
-- title:
--   KReal: cas one
-- statement:
--   The KReal construction uses the cas one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasA.lean#L72-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasA.lean#L72-L199

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasA
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

theorem PositivityTheory.KReal.cas_one {K I : Type} [Fintype K] [Fintype I] [DecidableEq I] (σ : K → K) (hσ : Function.Involutive σ)
    {M : Type} [AddCommGroup M] [Module ℂ M] (e : K → Module.End ℂ M) (X : I → Module.End ℂ M)
    (c : K → Matrix I I ℂ) (d c0 : ℝ)
    (h1 : ∀ k i, e k * X i - X i * e k = ∑ j, c k j i • X j)
    (h3 : ∀ k, c (σ k) = (c k)ᴴ)
    (h4 : ∑ k, c k * c (σ k) = (d : ℂ) • (1 : Matrix I I ℂ))
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : K → Module.End ℂ V) (hadj : ∀ k u v, ⟪ρ k u, v⟫_ℂ = ⟪u, ρ (σ k) v⟫_ℂ)
    (hc0 : ∑ k, ρ k * ρ (σ k) = (c0 : ℂ) • (1 : Module.End ℂ V))
    (ι : V →ₗ[ℂ] M) (hι : ∀ k v, ι (ρ k v) = e k (ι v))
    (h5 : ∀ t : ℝ, t ≤ c0 + d → ∀ x ∈ Submodule.span ℂ {y | ∃ i v, y = X i (ι v)},
      (∑ k, e k * e (σ k)) x = (t : ℂ) • x → x = 0)
    (Φ : I → V) (hΦ : ∀ Θ : I → V, ∑ i, X i (ι (Θ i)) = 0 → ∑ i, ⟪Φ i, Θ i⟫_ℂ = 0) :
    0 ≤ (∑ k, ∑ i, ∑ j, ⟪Φ i, c k i j • ρ (σ k) (Φ j)⟫_ℂ).re ∧
      ((∑ k, ∑ i, ∑ j, ⟪Φ i, c k i j • ρ (σ k) (Φ j)⟫_ℂ).re = 0 → Φ = 0) := by sorry
