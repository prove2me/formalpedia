-- Prove2me | Theorems.Thm_SAG_SmallStep_lyapunov_init
-- name    : SAG.SmallStep.lyapunov_init
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:27:06.151733+00:00
-- url     : https://prove2.me/theorems/3e09428f-f921-4526-af26-5d20cde9d0a3
-- title:
--   §A.5 Step 2, p. 23 — with $y^0=0$: $Q(\theta^0)=3\sigma^2/(4L^2)+\|x^0-x^*\|^2$
-- statement:
--   Let $n\ge1$, $L>0$, let $f_1,\dots,f_n:\mathbb R^p\to\mathbb R$ be differentiable with gradients $f'_i$, and let $x^*$ be a minimizer of $g=\frac1n\sum_if_i$. Let $Q$ be the Lyapunov function of §A.5 with $\alpha=\frac1{2nL}$ and put $\sigma^2=\frac1n\sum_{i=1}^n\|f'_i(x^*)\|^2$. For the initial state $\theta^0=(0,\dots,0,x^0)$ with all $y^0_i=0$,
--   $$
--   Q(\theta^0)=\frac{3\sigma^2}{4L^2}+\|x^0-x^*\|^2 .
--   $$
--
--   This evaluates the starting value of the Lyapunov function and produces the constant $9\sigma^2/(4L^2)$ of Proposition 1.
--
--   **Formalization Note** The page's computation uses $\sum_if'_i(x^*)=0$, which follows from $x^*$ minimizing $g$; the theorem assumes the minimality, not the gradient identity. (The page's intermediate display writes $\frac{(1-2n)\alpha}{n^2}$ where the definition of $A$ gives $\frac{(1-2n)\alpha^2}{n^2}$; that term vanishes at $y^0=0$.)
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, p. 23, §A.5 Step 2, "Initializing all the y_i^0 to 0, we get"

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAG_SmallStep_blockForm
import Definitions.Def_SAG_SmallStep_lyapunov

namespace SAG.SmallStep

/-- §A.5 Step 2 (arXiv:1202.6258v4, p. 23): with `α = 1/(2nL)` and the table initialized to
`y⁰ = 0`, `Q(θ⁰) = 3σ²/(4L²) + ‖x⁰ − x*‖²`, where `σ² = (1/n) ∑ᵢ ‖f'ᵢ(x*)‖²` and `x*` minimizes
`g`. -/
theorem lyapunov_init {p n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ) (hL : 0 < L)
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (xstar : EuclideanSpace ℝ (Fin p))
    (hmin : ∀ x, SAGA.Convex.fAvg f xstar ≤ SAGA.Convex.fAvg f x)
    (x0 : EuclideanSpace ℝ (Fin p)) :
    lyapunov f' (1 / (2 * (n : ℝ) * L)) xstar (fun _ => 0, x0)
      = 3 * ((1 / (n : ℝ)) * ∑ i, ‖f' i xstar‖ ^ 2) / (4 * L ^ 2) + ‖x0 - xstar‖ ^ 2 := by sorry

end SAG.SmallStep
