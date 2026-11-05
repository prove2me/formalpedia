-- Prove2me | Theorems.Thm_RouzeFranca_LearnGibbs_hasGradientAt_maxEntObjective
-- name    : RouzeFranca.LearnGibbs.hasGradientAt_maxEntObjective
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:47:33.293379+00:00
-- url     : https://prove2.me/theorems/1967f93c-6487-4f9e-9269-5dc871f0d42f
-- title:
--   §3.1 / Eq. (27) — $\nabla f(\mu)=\beta(e(\lambda)-e(\mu))$
-- statement:
--   Let $E_1,\dots,E_m$ be Hermitian observables on $n$ qubits, $\beta\in\mathbb R$ and $\lambda\in\mathbb R^m$, and let $f(\mu)=\log\mathcal Z(\mu)+\beta\sum_i\mu_ie_i(\lambda)$ be the maximum-entropy objective. Then $f$ is differentiable at every $\mu\in\mathbb R^m$, with gradient
--   $$
--   \nabla f(\mu)=\beta\bigl(e(\lambda)-e(\mu)\bigr),\qquad\text{i.e.}\quad (\nabla f(\mu))_i=\beta\operatorname{tr}\bigl[(\sigma(\lambda)-\sigma(\mu))E_i\bigr].
--   $$
--
--   Equivalently $\partial_{\mu_i}\log\mathcal Z(\mu)=-\beta\,e_i(\mu)$. The gradient vanishes exactly when the expectation values match, which is what the learning algorithm uses to select its output.
--
--   **Formalization Note** The gradient is taken with respect to the Euclidean inner product on $\mathbb R^m$.
--
--   Differences from the source:
--   - generalization: β > 0, μ ∈ B_ℓ∞(0,1), Gibbs state of linearly independent E_i with ∥E_i∥_∞ ≤ 1 → any real β, any μ, λ ∈ ℝ^m, any Hermitian E_i; reason: the identity holds for every Hermitian family and every parameter; the source's case is a special case
--   - encoding: ∇f → HasGradientAt on EuclideanSpace ℝ (Fin m); reason: Lean convention; same instances
-- source:
--   Rouzé, Stilck França, Learning quantum many-body systems from a few copies, arXiv:2107.03333v4, §3.1, p. 8 (unnumbered claim; the same identity is Eq. (27) of Lemma A.2, p. 16, whose Hessian formula (28) is not part of this item)

import Mathlib
import Definitions.Def_RouzeFranca_LearnGibbs_gibbs
import Definitions.Def_RouzeFranca_LearnGibbs_maxEntObjective

namespace RouzeFranca.LearnGibbs

/-- **§3.1 / Lemma A.2, Eq. (27) (gradient of the maximum-entropy objective).** For Hermitian
observables `E₁, …, E_m`, any inverse temperature `β` and any parameters `λ, μ ∈ ℝ^m`, the
objective `f(μ) = log Z(μ) + β ∑ᵢ μᵢ eᵢ(λ)` has gradient `∇f(μ) = β (e(λ) − e(μ))`.

Rouzé, Stilck França, arXiv:2107.03333v4, §3.1, p. 8: "If we define the function
f : µ ↦ log(Z(µ)) + β Σ_{i=1}^m µ_i e_i(λ), then ∇f = β(e(λ) − e(µ))"; the same identity is
Lemma A.2, Eq. (27), p. 16: "(∇f(µ))_i = β tr[(σ(λ) − σ(µ))E_i]".

**Formalization Note.** `lam` is the paper's `λ`. Stated for every real `β` and every `λ, μ`
(the paper's setting has `β > 0`, `‖λ‖∞, ‖μ‖∞ ≤ 1`, linearly independent `Eᵢ` with
`‖Eᵢ‖∞ ≤ 1`; none of these is needed). The gradient is with respect to the Euclidean inner
product on `ℝ^m`. -/
theorem hasGradientAt_maxEntObjective {n m : ℕ} (E : Fin m → Mat n)
    (hE : ∀ i, (E i).IsHermitian) (β : ℝ) (lam μ : EuclideanSpace ℝ (Fin m)) :
    HasGradientAt (maxEntObjective E β lam) (β • (expect E β lam - expect E β μ)) μ := by sorry

end RouzeFranca.LearnGibbs
