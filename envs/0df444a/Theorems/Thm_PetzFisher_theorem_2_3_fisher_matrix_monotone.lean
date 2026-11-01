-- Prove2me | Theorems.Thm_PetzFisher_theorem_2_3_fisher_matrix_monotone
-- name    : PetzFisher.theorem_2_3_fisher_matrix_monotone
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:28:23.164089+00:00
-- url     : https://prove2.me/theorems/97ded16c-e1df-4ced-b09d-ce6c9cd35509
-- title:
--   Theorem 2.3 — monotonicity of the quantum Fisher information matrix, $J_2(\theta)\le J_1(\theta)$
-- statement:
--   Let $f$ be a standard matrix monotone function, let $\beta:M_n\to M_m$ be a completely positive trace preserving mapping, and let $\mathcal M:=\{\rho(\theta)\in M_n:\theta\in G\}$, $G\subseteq\mathbb R^k$ open, be a differentiable $k$-parameter family of invertible density matrices such that $\beta(\rho(\theta))$ is invertible for every $\theta\in G$. Let $J_1(\theta)$ be the quantum Fisher information matrix (26) of $\mathcal M$ and $J_2(\theta)$ that of $\beta(\mathcal M):=\{\beta(\rho(\theta)):\theta\in G\}$. Then for every $\theta\in G$
--
--   $$
--   J_2(\theta)\le J_1(\theta),
--   $$
--
--   that is, $J_1(\theta)-J_2(\theta)$ is a positive semidefinite (real symmetric) $k\times k$ matrix.
--
--   This is the monotonicity of the quantum Fisher information under coarse-graining: no quantum channel, in particular no measurement, can increase the information a family of states carries about its parameters. It holds simultaneously for every monotone Fisher information (SLD, Bogoliubov–Kubo–Mori, maximal, …), and its special case where $\beta$ is a measurement gives the comparison of quantum and classical Fisher information.
--
--   **Formalization Note** $f$ is operator monotone on positive definite matrices of every size, positive and symmetric ($xf(x^{-1})=f(x)$) on $(0,\infty)$; the normalization $f(1)=1$ is not required. $\beta$ is complex linear and completely positive ($\mathrm{id}_r\otimes\beta$ positive for every $r$) and trace preserving. $\rho$ is entrywise differentiable on $G$ with $\rho(\theta)$ positive definite of trace $1$ there. The order on real symmetric matrices is tested on real vectors, which for a real symmetric matrix is equivalent to the paper's complex vectors $a$.
--
--   Differences from the source:
--   - generalization: f standard ((i) monotone on positive matrices, (ii) xf(x⁻¹) = f(x), f(1) = 1) → operator monotone on positive definite matrices, positive and symmetric on (0,∞), f(1) = 1 dropped; reason: every standard f is positive (2x/(x+1) ≤ f(x), p.8); the other changes weaken the hypothesis, so the printed case is an instance
--   - generalization: smooth k-dimensional manifold → entrywise differentiable on an open G ⊆ ℝᵏ, no injectivity or immersion condition; reason: only the partial derivatives are used; a smooth parametrization is an instance
--   - reading: β(ρ(θ)) unrestricted → β(ρ(θ)) positive definite for θ ∈ G; reason: the Fisher information matrix (25)–(26) of β(𝓜) is defined only for invertible density matrices (p.14) and 𝕁^f_D only for positive invertible D (p.7)
--   - encoding: J(θ)_ij = Tr (𝕁^f_{ρ(θ)})^{-1}(∂_iρ)(∂_jρ) → its real part (published metric); reason: the trace is real for symmetric f and self-adjoint tangent vectors (p.7, (11))
--   - encoding: J₂(θ) ≤ J₁(θ) → J₁(θ) − J₂(θ) positive semidefinite over ℝ; reason: the order of real symmetric matrices; real and complex test vectors give the same order
--   - encoding: Mₙ, Mₘ, ℝᵏ → complex matrices over finite index types, Fin k → ℝ; reason: Lean convention, same instances
-- source:
--   Petz–Ghinea, Introduction to quantum Fisher information, arXiv:1008.2417v1, Theorem 2.3, p.15

import Mathlib
import Definitions.Def_PetzFisher_fisherMatrix
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

open scoped Matrix ComplexOrder

namespace PetzFisher

/-- Petz–Ghinea, *Introduction to quantum Fisher information*, arXiv:1008.2417v1, Theorem 2.3, p.15:
"Let `β : Mₙ → Mₘ` be a completely positive trace preserving mapping and let
`𝓜 := {ρ(θ) ∈ Mₙ : θ ∈ G}` be a smooth `k`-dimensional manifold of invertible density matrices.
For the Fisher information matrix `J₁(θ)` of `𝓜` and for Fisher information matrix `J₂(θ)` of
`β(𝓜) := {β(ρ(θ)) : θ ∈ G}` we have the monotonicity relation `J₂(θ) ≤ J₁(θ)`."

Here `f` is a standard matrix monotone function (standing assumption of §2, p.10), `J(θ)` is the
Fisher information matrix (26) of p.14, and `J₂(θ) ≤ J₁(θ)` is the order of real symmetric `k × k`
matrices: `J₁(θ) − J₂(θ)` is positive semidefinite.

**Formalization Note.** `Mₙ`, `Mₘ` are `Matrix I I ℂ`, `Matrix J J ℂ` for finite types `I`, `J`;
CPTP is the published `Dependency50.P28.CPTP`. `f` is a published `Bridge50.P31.MetricGenerator`
(operator monotone, positive and symmetric `x f(x^{-1}) = f(x)` on `(0, ∞)`); the normalization
`f(1) = 1` of a standard function is not required, so the statement covers every positive multiple of
a standard function. The smooth `k`-dimensional manifold is a family `ρ : ℝᵏ → Mₙ` that is entrywise
differentiable on an open set `G` and takes invertible (positive definite) density matrices there;
no injectivity or immersion condition is imposed. `β(ρ(θ))` is assumed invertible, the condition
under which the Fisher information matrix of `β(𝓜)` is defined (p.14: "manifold of invertible
density matrices"; p.7: `𝕁^f_D` for "a positive invertible matrix"). -/
theorem theorem_2_3_fisher_matrix_monotone {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] {k : ℕ} (f : ℝ → ℝ)
    (hf : QAlgorithms.Papers.Independent.Bridge50.P31.MetricGenerator f)
    (β : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ)
    (hβ : QAlgorithms.Papers.Independent.Dependency50.P28.CPTP β)
    (G : Set (Fin k → ℝ)) (hG : IsOpen G) (ρ : (Fin k → ℝ) → Matrix I I ℂ)
    (hρ : ∀ θ ∈ G, (ρ θ).PosDef ∧ (ρ θ).trace = 1)
    (hdiff : ∀ a b, DifferentiableOn ℝ (fun θ => ρ θ a b) G)
    (hβρ : ∀ θ ∈ G, (β (ρ θ)).PosDef) :
    ∀ θ ∈ G, (fisherMatrix f ρ θ - fisherMatrix f (fun θ' => β (ρ θ')) θ).PosSemidef := by sorry

end PetzFisher
