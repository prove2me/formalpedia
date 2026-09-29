-- Prove2me | Theorems.Thm_SPOBounds_Margin_maurer_vector_contraction
-- name    : SPOBounds.Margin.maurer_vector_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:34:28.960565+00:00
-- url     : https://prove2.me/theorems/8ad4abd3-fdc3-437d-a5ce-2c8d6cb38b02
-- title:
--   Eq. (7) with $C=\sqrt2$ — Maurer's vector contraction inequality
-- statement:
--   Fix a feature sample $x_1,\dots,x_n\in\mathcal X$ and a class $\mathcal H$ of functions from $\mathcal X$ to $\mathbb R^d$, where $\mathbb R^d$ carries the Euclidean norm $\|\cdot\|_2$. Let $\Phi_1,\dots,\Phi_n:\mathbb R^d\to\mathbb R$ be $L$-Lipschitz:
--   $$|\Phi_i(u)-\Phi_i(v)|\le L\,\|u-v\|_2 \qquad\text{for all } u,v\in\mathbb R^d .$$
--   Let $\sigma_1,\dots,\sigma_n$ be i.i.d. Rademacher signs and $\boldsymbol\sigma_1,\dots,\boldsymbol\sigma_n$ i.i.d. Rademacher vectors in $\{\pm1\}^d$. Then
--   $$\mathbb E_\sigma\Big[\sup_{f\in\mathcal H}\frac1n\sum_{i=1}^n\sigma_i\Phi_i(f(x_i))\Big]\;\le\;\sqrt2\,L\cdot\mathbb E_{\boldsymbol\sigma}\Big[\sup_{f\in\mathcal H}\frac1n\sum_{i=1}^n\boldsymbol\sigma_i^\top f(x_i)\Big]=\sqrt2\,L\cdot\hat{\mathfrak R}^n(\mathcal H).$$
--
--   This is the vector contraction inequality of Maurer (2016), i.e. the paper's inequality (7) with constant $C=\sqrt2$. It is the tool that reduces the Rademacher complexity of a Lipschitz loss of a vector-valued predictor to the multivariate Rademacher complexity of the predictor class.
--
--   **Formalization Note** Predictions are continuous linear functionals on Euclidean $\mathbb R^d$ (their operator norm is the Euclidean norm, by the Riesz isometry), and $\boldsymbol\sigma_i^\top f(x_i)$ is $f(x_i)$ applied to $\boldsymbol\sigma_i$. The hypothesis that the multivariate sums $\sup_f\frac1n\sum_i\boldsymbol\sigma_i^\top f(x_i)$ are bounded above for every sign pattern is added so that $\hat{\mathfrak R}^n(\mathcal H)$ is the paper's (finite) quantity rather than Lean's junk value; it implies that $\{(f(x_1),\dots,f(x_n)):f\in\mathcal H\}$ is bounded, so the left-hand suprema are finite too. No condition $\Phi_i(0)=0$, symmetry of $\mathcal H$, or nonnegativity of $L$ is assumed; for empty $\mathcal H$ both sides are $0$.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, pp. 18–19, §4.2–4.3, Eq. (7) with C = √2 (A. Maurer, A vector-contraction inequality for Rademacher complexities, ALT 2016)

import Mathlib
import Definitions.Def_SPOBounds_Margin_Model
import Definitions.Def_SPOBounds_Margin_Degeneracy
import Definitions.Def_SPOBounds_Margin_Rademacher

namespace SPOBounds.Margin

/-- **Eq. (7) with `C = √2`** (arXiv:1905.11488v3, §4.2–4.3, pp. 18–19; Maurer 2016, the vector
contraction inequality). Fix a feature sample `x₁, …, xₙ` and a class `H` of maps from `X` to cost
vectors on `ℝ^d` (continuous linear functionals; their operator norm is the Euclidean norm). Let
`Φ₁, …, Φₙ` be `L`-Lipschitz with respect to that norm. If, for every sign matrix, the
multivariate Rademacher sums over `H` are bounded above, then
`𝔼_σ[sup_{f ∈ H} (1/n) ∑ᵢ σᵢ Φᵢ(f(xᵢ))] ≤ √2 · L · R̂ⁿ(H)`. -/
theorem maurer_vector_contraction {d n : ℕ} {X : Type*}
    (H : Set (X → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))) (x : Fin n → X)
    (Φ : Fin n → StrongDual ℝ (EuclideanSpace ℝ (Fin d)) → ℝ) (L : ℝ)
    (hΦ : ∀ i u v, |Φ i u - Φ i v| ≤ L * ‖u - v‖)
    (hB : ∀ σ : Fin n → Fin d → Bool,
      BddAbove (Set.range fun f : H => (1 / n : ℝ) *
        ∑ i, (f : X → StrongDual ℝ (EuclideanSpace ℝ (Fin d))) (x i) (signVec (σ i)))) :
    (1 / 2 ^ n : ℝ) * ∑ τ : Fin n → Bool,
        ⨆ f : H, (1 / n : ℝ) * ∑ i,
          (if τ i then (1 : ℝ) else -1) *
            Φ i ((f : X → StrongDual ℝ (EuclideanSpace ℝ (Fin d))) (x i))
      ≤ Real.sqrt 2 * L * empRademacherMulti H x := by sorry

end SPOBounds.Margin
