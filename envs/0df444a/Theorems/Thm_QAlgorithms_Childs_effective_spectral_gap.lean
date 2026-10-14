-- Prove2me | Theorems.Thm_QAlgorithms_Childs_effective_spectral_gap
-- name    : QAlgorithms.Childs.effective_spectral_gap
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:32:44.889766+00:00
-- url     : https://prove2.me/theorems/615cd062-8912-4fed-bd3a-6b26d4c3337a
-- title:
--   Effective spectral gap lemma
-- statement:
--   Let $\mathcal H$ be a finite-dimensional complex inner product space and let $\Pi$ and $\Delta$ be orthogonal projections on $\mathcal H$. Put $U = (2\Pi - I)(2\Delta - I)$, a unitary. For $\omega \ge 0$, let $P_\omega$ be the orthogonal projector onto the span of the eigenvectors of $U$ whose eigenvalues are $e^{i\theta}$ with $|\theta| < \omega$. If $|\phi\rangle \in \mathcal H$ is a unit vector with $\Delta|\phi\rangle = 0$, then
--
--   $$\|P_\omega \Pi |\phi\rangle\| \le \frac{\omega}{2}.$$
--
--   The lemma is the key step in showing that the phase-estimation algorithm built from a dual adversary solution rejects inputs with $f(x) = 0$: the start state has little weight on eigenvectors of small phase.
--
--   **Formalization Note** $\Pi$ and $\Delta$ are given as the orthogonal projections onto submodules $K$ and $L$; $2P - I$ is Mathlib's reflection through the subspace. The eigenvalue set is $\{e^{i\theta} : \theta \in \mathbb{R}, |\theta| < \omega\}$, which is the same set as with $\theta$ restricted to $(-\pi,\pi]$.
-- source:
--   Andrew Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, PDF p. 128, Lemma 24.3. https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_Adversary
set_option autoImplicit false

namespace QAlgorithms.Childs

open scoped NNReal ENNReal



/-- Childs, Lemma 24.3 (PDF p. 128), the effective spectral gap lemma. Let `Π` and `∆` be the
orthogonal projections onto subspaces `K` and `L` of a finite-dimensional complex inner product
space, `U = (2Π − I)(2∆ − I)`, `ω ≥ 0`, and `P_ω` the projector onto the span of the eigenvectors
of `U` with eigenvalues `e^{iθ}`, `|θ| < ω`. If `|ϕ⟩` is a unit vector with `∆|ϕ⟩ = 0`, then
`‖P_ω Π|ϕ⟩‖ ≤ ω/2`. -/
theorem effective_spectral_gap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (K L : Submodule ℂ E) (ω : ℝ) (hω : 0 ≤ ω) (ϕ : E)
    (hϕ : ‖ϕ‖ = 1) (hΔ : L.starProjection ϕ = 0) :
    ‖eigenProjection (reflProduct K L)
        {μ : ℂ | ∃ θ : ℝ, |θ| < ω ∧ μ = Complex.exp (θ * Complex.I)}
        (K.starProjection ϕ)‖ ≤ ω / 2 := by
  sorry

end QAlgorithms.Childs
