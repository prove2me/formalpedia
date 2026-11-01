-- Prove2me | Theorems.Thm_PetzFisher_fisher_quadratic_form_le
-- name    : PetzFisher.fisher_quadratic_form_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:28:44.583+00:00
-- url     : https://prove2.me/theorems/20161ba6-02dc-4da9-a6cb-ad559918ed95
-- title:
--   Proof of Theorem 2.3 — $\sum_{ij}J_2(\theta)_{ij}a_i\overline{a_j}\le\sum_{ij}J_1(\theta)_{ij}a_i\overline{a_j}$
-- statement:
--   Let $f$ be a standard matrix monotone function, $\beta:M_n\to M_m$ completely positive and trace preserving, $G\subseteq\mathbb R^k$ open, and $\theta\mapsto\rho(\theta)$ a differentiable family of invertible density matrices on $G$ whose image $\beta(\rho(\theta))$ is invertible for every $\theta\in G$. Let $J_1(\theta)$ be the Fisher information matrix (26) of $\mathcal M=\{\rho(\theta)\}$ and $J_2(\theta)$ that of $\beta(\mathcal M)=\{\beta(\rho(\theta))\}$. Then for every $\theta\in G$ and every $a\in\mathbb C^k$,
--
--   $$
--   \sum_{ij}J_2(\theta)_{ij}\,a_i\overline{a_j}\ \le\ \sum_{ij}J_1(\theta)_{ij}\,a_i\overline{a_j}.
--   $$
--
--   This is the outer inequality of the display in the proof of Theorem 2.3, where both sides are rewritten as $\langle\sum_ia_iB_i,\cdot\rangle$ forms and inequality (14) of Theorem 1.2 is applied to $A=\sum_ia_iB_i(\theta)$.
--
--   **Formalization Note** $f$ is operator monotone on positive definite matrices of every size, positive and symmetric ($xf(x^{-1})=f(x)$) on $(0,\infty)$; the normalization $f(1)=1$ is not required. The family is entrywise differentiable on $G$ and $\rho(\theta)$ is positive definite of trace $1$. The inequality is between complex numbers, $z\le w$ meaning that $w-z$ is real and nonnegative.
--
--   Differences from the source:
--   - generalization: f standard ((i) monotone on positive matrices, (ii) xf(x⁻¹) = f(x), f(1) = 1) → operator monotone on positive definite matrices, positive and symmetric on (0,∞), f(1) = 1 dropped; reason: every standard f is positive (2x/(x+1) ≤ f(x), p.8); the other changes weaken the hypothesis, so the printed case is an instance
--   - generalization: smooth k-dimensional manifold → entrywise differentiable on an open G ⊆ ℝᵏ, no injectivity or immersion condition; reason: only the partial derivatives are used; a smooth parametrization is an instance
--   - reading: β(ρ(θ)) unrestricted → β(ρ(θ)) positive definite for θ ∈ G; reason: the Fisher information matrix (25)–(26) of β(𝓜) is defined only for invertible density matrices (p.14) and 𝕁^f_D only for positive invertible D (p.7)
--   - encoding: J(θ)_ij = Tr (𝕁^f_{ρ(θ)})^{-1}(∂_iρ)(∂_jρ) → its real part (published metric); reason: the trace is real for symmetric f and self-adjoint tangent vectors (p.7, (11))
--   - encoding: Mₙ, Mₘ, ℝᵏ → complex matrices over finite index types, Fin k → ℝ; reason: Lean convention, same instances
-- source:
--   Petz–Ghinea, Introduction to quantum Fisher information, arXiv:1008.2417v1, proof of Theorem 2.3, display, p.15

import Mathlib
import Definitions.Def_PetzFisher_fisherMatrix
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

open scoped Matrix ComplexOrder ComplexConjugate

namespace PetzFisher

/-- Petz–Ghinea, *Introduction to quantum Fisher information*, arXiv:1008.2417v1, proof of
Theorem 2.3, display, p.15: "`Σ_{ij} J₂(θ)_{ij} a_i \overline{a_j} = Tr 𝕁^{-1}_{β(ρ(θ))} β(Σ_i a_i B_i(θ))
β(Σ_j \overline{a_j} B_j(θ)) = … ≤ … = Σ_{ij} J₁(θ)_{ij} a_i \overline{a_j}`, where (14) was used."

The outer inequality of the display: under the hypotheses of Theorem 2.3, for every `θ ∈ G` and
every complex vector `a ∈ ℂᵏ`,
`Σ_{ij} J₂(θ)_{ij} a_i \overline{a_j} ≤ Σ_{ij} J₁(θ)_{ij} a_i \overline{a_j}` in `ℂ` (`ComplexOrder`),
where `J₁(θ)` is the Fisher information matrix of `θ ↦ ρ(θ)` and `J₂(θ)` that of `θ ↦ β(ρ(θ))`.

**Formalization Note.** Hypotheses as in `theorem_2_3_fisher_matrix_monotone`: `f` is a
`Bridge50.P31.MetricGenerator` (operator monotone, positive and symmetric `x f(x^{-1}) = f(x)` on
`(0, ∞)`; the normalization `f(1) = 1` is not required), `β` is CPTP, `ρ` takes invertible density
matrices on the open set `G ⊆ ℝᵏ` and is entrywise differentiable there, and `β(ρ(θ))` is
invertible on `G`. -/
theorem fisher_quadratic_form_le {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] {k : ℕ} (f : ℝ → ℝ)
    (hf : QAlgorithms.Papers.Independent.Bridge50.P31.MetricGenerator f)
    (β : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ)
    (hβ : QAlgorithms.Papers.Independent.Dependency50.P28.CPTP β)
    (G : Set (Fin k → ℝ)) (hG : IsOpen G) (ρ : (Fin k → ℝ) → Matrix I I ℂ)
    (hρ : ∀ θ ∈ G, (ρ θ).PosDef ∧ (ρ θ).trace = 1)
    (hdiff : ∀ a b, DifferentiableOn ℝ (fun θ => ρ θ a b) G)
    (hβρ : ∀ θ ∈ G, (β (ρ θ)).PosDef) :
    ∀ θ ∈ G, ∀ a : Fin k → ℂ,
      ∑ i, ∑ j, ((fisherMatrix f (fun θ' => β (ρ θ')) θ i j : ℝ) : ℂ) * a i * conj (a j) ≤
        ∑ i, ∑ j, ((fisherMatrix f ρ θ i j : ℝ) : ℂ) * a i * conj (a j) := by sorry

end PetzFisher
