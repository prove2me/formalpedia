-- Prove2me | Theorems.Thm_SpectralSharpness_NormalWindow_lemma_9_1
-- name    : SpectralSharpness.NormalWindow.lemma_9_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:21:44.999217+00:00
-- url     : https://prove2.me/theorems/92dda627-0e6a-43a0-b49c-fd6051c4db87
-- title:
--   Lemma 9.1 — directional Markov/Bernstein inequality: $|\partial_v f|\le dA$ for ball spectrum, $\le d\|v\|_1A\le\sqrt n\,dA$ for cube spectrum
-- statement:
--   Let $n\ge0$, $d\ge0$ and $A\in\mathbb R$. Points of $\mathbb T^n$ are represented in $\mathbb R^n$ with the Euclidean norm.
--
--   1. **Ball spectrum.** Let $f$ be a real trigonometric polynomial on $\mathbb T^n$ with spectrum in the Euclidean ball $B_d=\{k\in\mathbb Z^n:\|k\|_2\le d\}$, and suppose $\|f\|_\infty\le A$, i.e. $|f(x)|\le A$ for all $x$. Then for every unit vector $v\in\mathbb R^n$ and every point $x_0$,
--   $$
--   |\partial_v f(x_0)|\le d\,A,
--   $$
--   and equivalently, in gradient form, $\|\nabla f(x_0)\|_2\le d\,A$ for every $x_0$.
--
--   2. **Cube spectrum.** If instead $f$ has spectrum in the cube $\{k:\|k\|_\infty\le d\}$ and $|f|\le A$, then for every unit vector $v$ and every $x_0$,
--   $$
--   |\partial_v f(x_0)|\le d\,\|v\|_1\,A\le\sqrt n\,d\,A,\qquad \|v\|_1=\sum_{i=1}^n|v_i| .
--   $$
--
--   The constant $dA$ for the Euclidean ball does not depend on the dimension $n$; it is the one-dimensional Bernstein constant. A cube spectrum of the same radius can cost the factor $\|v\|_1$, up to $\sqrt n$. Lemma 9.1 bounds the slope of the classifier along every line, which is what forces a window of width $2\gamma/(dA)$ in Theorem 9.3.
--
--   **Formalization Note** $\partial_v f(x_0)$ is `fderiv ℝ f x₀ v` and $\nabla f(x_0)$ is Mathlib's `gradient f x₀` on `EuclideanSpace ℝ (Fin n)`. Differentiability of $f$ is not assumed: $f$ is a finite exponential sum, hence smooth.
--
--   Differences from the source:
--   - generalization: d is the degree (bandwidth) of the classifier → any real d ≥ 0; reason: B_d = {k : ∥k∥₂ ≤ d} is defined by an inequality that makes sense for real d, and every source instance has d ≥ 0
--   - encoding: f band-limited on 𝕋ⁿ = [−π, π)ⁿ → a real function on ℝⁿ equal to a finite sum of c_k e^{i k·x} with k ∈ ℤⁿ in the ball (or cube); reason: such sums are exactly the 2π-periodic extensions of the source's band-limited f; sup norms over ℝⁿ and over 𝕋ⁿ agree
--   - encoding: ∥ |∇f| ∥∞ ≤ dA → ‖∇f(x₀)‖₂ ≤ dA for every x₀; reason: a supremum over x₀ is at most dA iff every value is
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript (STOC 2027 submission #122; SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, Lemma 9.1, p. 27

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_BandLimited

namespace SpectralSharpness.NormalWindow

/-- Lemma 9.1 (directional Markov/Bernstein inequality). Let `d ≥ 0` and `A` be real.
(Ball) If the real trigonometric polynomial `f` on `𝕋ⁿ` has spectrum in the Euclidean ball
`‖k‖₂ ≤ d` and `|f| ≤ A`, then `|∂_v f(x₀)| ≤ d A` for every unit vector `v` and every `x₀`,
and `‖∇f(x₀)‖₂ ≤ d A` for every `x₀`.
(Cube) If instead the spectrum lies in the cube `‖k‖_∞ ≤ d` and `|f| ≤ A`, then for every
unit vector `v` and every `x₀`, `|∂_v f(x₀)| ≤ d ‖v‖₁ A ≤ √n d A`. -/
theorem lemma_9_1 {n : ℕ} (d A : ℝ) (hd : 0 ≤ d) :
    (∀ f : EuclideanSpace ℝ (Fin n) → ℝ, IsBandLimitedBall d f → (∀ x, |f x| ≤ A) →
      (∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → ∀ x₀, |fderiv ℝ f x₀ v| ≤ d * A) ∧
      (∀ x₀, ‖gradient f x₀‖ ≤ d * A)) ∧
    (∀ f : EuclideanSpace ℝ (Fin n) → ℝ, IsBandLimitedCube d f → (∀ x, |f x| ≤ A) →
      ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → ∀ x₀,
        |fderiv ℝ f x₀ v| ≤ d * (∑ i, |v i|) * A ∧
        d * (∑ i, |v i|) * A ≤ Real.sqrt n * d * A) := by sorry

end SpectralSharpness.NormalWindow
