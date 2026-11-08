-- Prove2me | Theorems.Thm_UniversalSubmod_claim_A_1
-- name    : UniversalSubmod.claim_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:51:32.453705+00:00
-- url     : https://prove2.me/theorems/8d9c5268-6c2a-45b6-b7fb-32ab32dd5e05
-- title:
--   Claim A.1 — Gaussian integration by parts $\mathbb E[Ug(V)]=\sum_j\mathrm{Cov}[U,V_j]\,\mathbb E[\partial_jg(V)]$
-- statement:
--   Suppose $(U,V_1,\dots,V_n)$ is a centered $(n+1)$-variate Gaussian vector and let $g:\mathbb R^n\to\mathbb R$ be continuously differentiable with bounded partial derivatives. Then, for $V=(V_1,\dots,V_n)$,
--   $$
--   \mathbb E\big[U\,g(V)\big]=\sum_{j=1}^n\mathrm{Cov}[U,V_j]\;\mathbb E\big[\partial_jg(V)\big].
--   $$
--   The function $g$ itself need not be bounded; it grows at most linearly.
--
--   This identity differentiates the Gaussian interpolation $t\mapsto\mathbb E[h(\sqrt{1-t}X+\sqrt tY)]$ in the proof of Theorem 2.3.
--
--   **Formalization Note** "Centered Gaussian" is `HasGaussianLaw` of the pair $(U,V)$ under a probability measure together with $\mathbb E[U]=0$ and $\mathbb E[V_j]=0$. $\partial_jg(x)$ is the Fréchet derivative of $g$ at $x$ applied to the $j$-th coordinate vector. The platform theorem `GaussianMatrix.gaussian_integration_by_parts` assumes $g$ bounded and is therefore a special case.
--
--   Differences from the source:
--   - encoding: a centered $(n+1)$-variate Gaussian $(U,V)$ → `HasGaussianLaw (fun ω => (U ω, fun j => V j ω)) P` with $\int U=0$, $\int V_j=0$; reason: joint Gaussian law plus zero means
--   - encoding: bounded partial derivatives → $\exists C,\ \forall x\ j,\ |\partial_jg(x)|\le C$; reason: the same condition
--   - encoding: $\mathrm{Cov}$, $\mathbb E$ → Mathlib's `cov[U, V j; P]` and Bochner integrals against $P$; reason: all integrands are integrable for a Gaussian vector and $g$ of linear growth
--   - encoding: $\mathbb R^n$ and $\partial_jg(x)$ → `Fin n → ℝ` and `fderiv ℝ g x (Pi.single j 1)`; reason: the same space and, for $C^1$ $g$, the classical partial derivative
-- source:
--   Adamczyk, Ueltzen, Vondrák, Optimal universal sets for submodular functions, manuscript (Nov. 3, 2026; sha256 8a53c0912e8ad39b1019cbabfbde98980fd3eea456a8c7e5b28eb55d58343714), Claim A.1, p.19

import Mathlib

namespace UniversalSubmod

open MeasureTheory ProbabilityTheory

/-- **Claim A.1** (Gaussian integration by parts; Adamczyk, Ueltzen, Vondrák, *Optimal universal
sets for submodular functions*, manuscript of November 3, 2026, Claim A.1, p.19). Suppose
`(U, V₁, …, Vₙ)` is a centered `(n+1)`-variate Gaussian, and let `g : ℝ^n → ℝ` be continuously
differentiable with bounded partial derivatives. Then for `V = (V₁, …, Vₙ)`,
`E[U g(V)] = ∑_{j=1}^n Cov[U, V_j] E[∂_j g(V)]`.

**Formalization Note.** "Centered `(n+1)`-variate Gaussian" is `HasGaussianLaw` of the pair
`(U, V) : Ω → ℝ × ℝ^n` under a probability measure `P` together with `E[U] = 0` and `E[V_j] = 0`.
`∂_j g(x)` is `fderiv ℝ g x (e_j)`. `g` itself is not assumed bounded. -/
theorem claim_A_1 {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → ℝ) (V : Fin n → Ω → ℝ)
    (hUV : HasGaussianLaw (fun ω => (U ω, fun j => V j ω)) P)
    (hU0 : ∫ ω, U ω ∂P = 0) (hV0 : ∀ j, ∫ ω, V j ω ∂P = 0)
    (g : (Fin n → ℝ) → ℝ) (hg : ContDiff ℝ 1 g)
    (hgb : ∃ C : ℝ, ∀ x j, |fderiv ℝ g x (Pi.single j (1 : ℝ))| ≤ C) :
    ∫ ω, U ω * g (fun j => V j ω) ∂P =
      ∑ j, cov[U, V j; P] * ∫ ω, fderiv ℝ g (fun l => V l ω) (Pi.single j (1 : ℝ)) ∂P := by sorry

end UniversalSubmod
