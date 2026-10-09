-- Prove2me | Theorems.Thm_SGDKaczmarz_SGD_expected_gradient
-- name    : SGDKaczmarz.SGD.expected_gradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:29:22.877843+00:00
-- url     : https://prove2.me/theorems/28537d65-bdb6-4227-b1ad-4d15a6629007
-- title:
--   Proof of Theorem 2.1, p. 22 — E∇f_i(x) = ∇F(x): F = E f_i is differentiable with gradient E∇f_i
-- statement:
--   Let $\mathcal D$ be a probability distribution on an index space $I$ and $\mathcal H$ a separable real Hilbert space. Let $f_i : \mathcal H \to \mathbb R$, $i \in I$, be differentiable with $\nabla f_i$ Lipschitz with constant $L_i$ (assumption (1)), where $L_i \le \sup L$ almost surely. Assume that $F(x) = \mathbb E f_i(x)$ is finite for every $x$, that $i \mapsto \nabla f_i(x)$ is measurable for every $x$, and that for some point $x_\star$
--   $$\sigma^2 = \mathbb E\|\nabla f_i(x_\star)\|_2^2 < \infty.$$
--   Then $F$ is differentiable at every $x \in \mathcal H$, with
--   $$\nabla F(x) = \mathbb E\,\nabla f_i(x).$$
--
--   This is the step "Then $\mathbb E\nabla f_i(x) = \nabla F(x)$" of the proof of Theorem 2.1: the stochastic gradient is an unbiased estimate of the gradient of the objective.
--
--   **Formalization Note** The conclusion is that $F$ has gradient $\mathbb E\nabla f_i(x)$ at $x$ (Mathlib's `HasGradientAt`), which includes the differentiability of $F$; $\mathbb E\nabla f_i(x)$ is a Bochner integral in $\mathcal H$. The finiteness of $\sigma^2$ is the page's standing reading of $\sigma^2$ as a number; $x_\star$ need not be a minimizer here. Separability of $\mathcal H$ (second countability) makes the gradient maps strongly measurable.
-- source:
--   Needell, Srebro & Ward, Stochastic gradient descent, weighted sampling, and the randomized Kaczmarz algorithm, arXiv:1310.5715v5, proof of Theorem 2.1 (Appendix A.2), "Then E∇f_i(x) = ∇F(x)", p. 22

import Mathlib
import Definitions.Def_SGDKaczmarz_SGD_Setting

open MeasureTheory
open scoped NNReal ENNReal InnerProductSpace

namespace SGDKaczmarz.SGD

/-- Proof of Theorem 2.1 (Appendix A.2), p. 22, "Then E∇f_i(x) = ∇F(x)": under assumption (1) with
`L_i ≤ sup L` a.s., `F(x) = E f_i(x)` finite and `σ² = E‖∇f_i(x⋆)‖² < ∞`, the objective `F` has
gradient `E ∇f_i(x)` at every `x`. -/
theorem expected_gradient {I : Type*} [MeasurableSpace I] (D : Measure I) [IsProbabilityMeasure D]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (f : I → H → ℝ) (L : I → ℝ≥0)
    (hdiff : ∀ i, Differentiable ℝ (f i))
    (hlip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (supL : ℝ) (hsup : ∀ᵐ i ∂D, (L i : ℝ) ≤ supL)
    (hint : ∀ x, Integrable (fun i => f i x) D)
    (hmeas : ∀ x, Measurable (fun i => gradient (f i) x))
    (xstar : H) (hσ : residual D f xstar < ⊤) :
    ∀ x, HasGradientAt (objective D f) (∫ i, gradient (f i) x ∂D) x := by sorry

end SGDKaczmarz.SGD
