-- Prove2me | Theorems.Thm_SAG_SmallStep_lyapunov_linear_rate
-- name    : SAG.SmallStep.lyapunov_linear_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:26:48.528472+00:00
-- url     : https://prove2.me/theorems/a221ab6d-cef1-4b7b-b8e5-70469aef0188
-- title:
--   §A.5 Step 1, p. 22 — $\mathbb EQ(\theta^k)\le(1-\mu/(8nL))^kQ(\theta^0)$
-- statement:
--   Under the assumptions of the one-step contraction (each $f_i$ convex with $L$-Lipschitz gradient, $L>0$; $g$ $\mu$-strongly convex, $\mu>0$; $x^*$ the minimizer of $g$; $n\ge1$), let $Q$ be the Lyapunov function of §A.5 with $\alpha=\frac1{2nL}$. Run SAG with step size $\alpha$ from an arbitrary initial state $\theta^0$, with indices $i_1,\dots,i_k$ independent and uniform on $\{1,\dots,n\}$. Then for every $k\ge0$
--   $$
--   \mathbb E\,Q(\theta^k)\le\Big(1-\frac{\mu}{8nL}\Big)^kQ(\theta^0).
--   $$
--
--   Combined with the domination $Q\ge\frac13\|x-x^*\|^2$ and the value of $Q$ at the zero-initialized start, this gives Proposition 1.
--
--   **Formalization Note** The expectation is `SAGA.Convex.expectIdx n k`, the uniform average over all index sequences $(i_1,\dots,i_k)\in\{1,\dots,n\}^k$, which is the law of $k$ i.i.d. uniform indices. The initial state is arbitrary (the page applies it to $y^0=0$).
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, p. 22, §A.5 Step 1, last display of Step 1

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_sagaRun
import Definitions.Def_SAG_SmallStep_run
import Definitions.Def_SAG_SmallStep_blockForm
import Definitions.Def_SAG_SmallStep_lyapunov

namespace SAG.SmallStep

/-- §A.5 Step 1 (arXiv:1202.6258v4, p. 22): with `α = 1/(2nL)`, from any initial state `θ⁰`,
`E Q(θᵏ) ≤ (1 − μ/(8nL))ᵏ Q(θ⁰)`, the expectation being over `k` i.i.d. uniform indices. -/
theorem lyapunov_linear_rate {p n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ)
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hlip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hsc : ConvexOn ℝ Set.univ (fun x => SAGA.Convex.fAvg f x - μ / 2 * ‖x‖ ^ 2))
    (xstar : EuclideanSpace ℝ (Fin p))
    (hmin : ∀ x, SAGA.Convex.fAvg f xstar ≤ SAGA.Convex.fAvg f x)
    (θ0 : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) (k : ℕ) :
    SAGA.Convex.expectIdx n k
        (fun js => lyapunov f' (1 / (2 * (n : ℝ) * L)) xstar
          (runFrom f' (1 / (2 * (n : ℝ) * L)) θ0 js))
      ≤ (1 - μ / (8 * (n : ℝ) * L)) ^ k * lyapunov f' (1 / (2 * (n : ℝ) * L)) xstar θ0 := by sorry

end SAG.SmallStep
