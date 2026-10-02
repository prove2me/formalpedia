-- Prove2me | Theorems.Thm_TeschlQM_Spectral_bounded_functional_calculus
-- name    : TeschlQM.Spectral.bounded_functional_calculus
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:28:32.014765+00:00
-- url     : https://prove2.me/theorems/f3e5b3aa-2c72-4f5a-a971-b6db8497150c
-- title:
--   Theorem 3.1 — the bounded functional calculus of a projection-valued measure
-- statement:
--   Let $P$ be a projection-valued measure on a complex Hilbert space $\mathfrak H$, and for a bounded Borel function $f \in B(\mathbb{R})$ let $P(f) = \int_{\mathbb{R}} f(\lambda)\,dP(\lambda) \in \mathfrak L(\mathfrak H)$. Then the map
--   $$P : B(\mathbb{R}) \to \mathfrak L(\mathfrak H), \qquad f \mapsto \int_{\mathbb{R}} f(\lambda)\, dP(\lambda)$$
--   is a $C^*$-algebra homomorphism of norm one: $P(1) = \mathbb{I}$, $P(f+g) = P(f) + P(g)$, $P(cf) = cP(f)$, $P(fg) = P(f)P(g)$, $P(f^*) = P(f)^*$ and $\|P(f)\| \le \sup_{\lambda} |f(\lambda)|$ for all $f, g \in B(\mathbb{R})$, $c \in \mathbb{C}$. Moreover, for $f, g \in B(\mathbb{R})$ and $\varphi, \psi \in \mathfrak H$,
--   $$\langle P(g)\varphi, P(f)\psi\rangle = \int_{\mathbb{R}} g^*(\lambda) f(\lambda)\, d\mu_{\varphi,\psi}(\lambda) \qquad (3.21).$$
--   Finally, if $f_n \in B(\mathbb{R})$, $f_n(x) \to f(x)$ for every $x$, and $\sup_{\lambda\in\mathbb{R}} |f_n(\lambda)|$ is bounded in $n$, then $P(f_n)\psi \to P(f)\psi$ for every $\psi \in \mathfrak H$ (strong convergence).
--
--   This is the functional calculus for bounded functions on which the unbounded calculus and the spectral theorem are built.
--
--   **Formalization Note.** $f^*$ is the pointwise complex conjugate (`star f`), $P(f)^*$ the Hilbert-space adjoint (`star` on `H →L[ℂ] H`). The sup norm $\sup_\lambda |f(\lambda)|$ is the real supremum `⨆ x, ‖f x‖`, which is the true supremum since $f$ is bounded. "Norm one" is the bound $\|P(f)\| \le \|f\|_\infty$ together with $P(1) = \mathbb{I}$, which has norm one when $\mathfrak H \ne \{0\}$. The integral against $\mu_{\varphi,\psi}$ is `spectralForm`, the polarization (3.15) of four spectral-measure integrals. In the convergence clause the limit $f$ is not assumed measurable or bounded: both follow from the hypotheses.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 90, Theorem 3.1

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Spectral_spectralMeasure
import Definitions.Def_TeschlQM_Spectral_boundedSpectralIntegral

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TeschlQM.Spectral

/-- Teschl, p. 90, Theorem 3.1. For a projection-valued measure `P`, the map
`f ↦ P(f) = ∫_ℝ f(λ) dP(λ)` from the bounded Borel functions `B(ℝ)` (sup norm) to `𝔏(H)` is a
unital C*-algebra homomorphism (linear, multiplicative, `P(f*) = P(f)*`) of norm one
(`‖P(f)‖ ≤ sup_λ |f(λ)|`, attained at `f = 1` when `H ≠ 0`), satisfies (3.21)
`⟨P(g)φ, P(f)ψ⟩ = ∫ g* f dμ_{φ,ψ}`, and `P(fₙ) → P(f)` strongly whenever `fₙ → f` pointwise
with `sup_λ |fₙ(λ)|` bounded in `n`. -/
theorem bounded_functional_calculus {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) (hP : TeschlQM.Shared.IsProjValuedMeasure P) :
    boundedSpectralIntegral P 1 = 1 ∧
    (∀ f g : ℝ → ℂ, IsBoundedBorel f → IsBoundedBorel g →
      boundedSpectralIntegral P (f + g) =
          boundedSpectralIntegral P f + boundedSpectralIntegral P g ∧
      boundedSpectralIntegral P (f * g) =
          boundedSpectralIntegral P f * boundedSpectralIntegral P g) ∧
    (∀ (c : ℂ) (f : ℝ → ℂ), IsBoundedBorel f →
      boundedSpectralIntegral P (c • f) = c • boundedSpectralIntegral P f) ∧
    (∀ f : ℝ → ℂ, IsBoundedBorel f →
      boundedSpectralIntegral P (star f) = star (boundedSpectralIntegral P f)) ∧
    (∀ f : ℝ → ℂ, IsBoundedBorel f → ‖boundedSpectralIntegral P f‖ ≤ ⨆ x, ‖f x‖) ∧
    (∀ f g : ℝ → ℂ, IsBoundedBorel f → IsBoundedBorel g → ∀ φ ψ : H,
      ⟪boundedSpectralIntegral P g φ, boundedSpectralIntegral P f ψ⟫_ℂ =
        spectralForm P φ ψ (star g * f)) ∧
    (∀ (fs : ℕ → ℝ → ℂ) (f : ℝ → ℂ), (∀ n, IsBoundedBorel (fs n)) →
      (∀ x, Filter.Tendsto (fun n => fs n x) Filter.atTop (nhds (f x))) →
      (∃ C : ℝ, ∀ n x, ‖fs n x‖ ≤ C) →
      ∀ ψ : H, Filter.Tendsto (fun n => boundedSpectralIntegral P (fs n) ψ) Filter.atTop
        (nhds (boundedSpectralIntegral P f ψ))) := by sorry

end TeschlQM.Spectral
