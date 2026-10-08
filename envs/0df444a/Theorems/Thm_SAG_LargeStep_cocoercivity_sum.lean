-- Prove2me | Theorems.Thm_SAG_LargeStep_cocoercivity_sum
-- name    : SAG.LargeStep.cocoercivity_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:25:22.529614+00:00
-- url     : https://prove2.me/theorems/401cca97-3d2b-4acd-bc03-13ef3f30154b
-- title:
--   §A.6 Step 1 — summed co-coercivity ‖f′(x) − f′(x*)‖² ≤ ∑ᵢ L⟨f′ᵢ(x) − f′ᵢ(x*), x − x*⟩ = nL⟨g′(x) − g′(x*), x − x*⟩
-- statement:
--   Throughout, $f_1,\dots,f_n:\mathbb R^p\to\mathbb R$ ($n\ge1$) are convex and differentiable with $L$-Lipschitz gradients $f_i'$, the average $g=\frac1n\sum_i f_i$ is $\mu$-strongly convex ($x\mapsto g(x)-\frac\mu2\|x\|^2$ is convex, $\mu>0$), $x^*$ minimizes $g$, $g'=\frac1n\sum_i f_i'$ and $\sigma^2=\frac1n\sum_i\|f_i'(x^*)\|^2$.
--
--   For every $x\in\mathbb R^p$,
--   $$\sum_{i=1}^n\|f_i'(x)-f_i'(x^*)\|^2\le\sum_{i=1}^nL\,(f_i'(x)-f_i'(x^*))^\top(x-x^*)=nL\,(g'(x)-g'(x^*))^\top(x-x^*).$$
--
--   The inequality is the co-coercivity of the gradient of each convex $L$-smooth $f_i$, summed over $i$; the proof of Proposition 2 applies it at $x=x^{k-1}$ to control the term $\|f'(x^{k-1})-f'(x^*)\|^2$ produced by Lemma 1.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, p. 24, §A.6 Step 1, last display

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAG_LargeStep_setting

namespace SAG.LargeStep

/-- §A.6 Step 1, p. 24, last display: summed co-coercivity,
`∑ᵢ ‖f'ᵢ(x) − f'ᵢ(x*)‖² ≤ ∑ᵢ L ⟪f'ᵢ(x) − f'ᵢ(x*), x − x*⟫ = nL ⟪g'(x) − g'(x*), x − x*⟫`. -/
theorem cocoercivity_sum {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L μ : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (h : Assumptions f f' L μ xstar)
    (x : EuclideanSpace ℝ (Fin p)) :
    ∑ i, ‖f' i x - f' i xstar‖ ^ 2 ≤ ∑ i, L * inner ℝ (f' i x - f' i xstar) (x - xstar)
      ∧ ∑ i, L * inner ℝ (f' i x - f' i xstar) (x - xstar)
        = (n : ℝ) * L * inner ℝ (SAGA.Convex.gradAvg f' x - SAGA.Convex.gradAvg f' xstar)
            (x - xstar) := by sorry

end SAG.LargeStep
