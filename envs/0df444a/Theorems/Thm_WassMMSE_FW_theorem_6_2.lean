-- Prove2me | Theorems.Thm_WassMMSE_FW_theorem_6_2
-- name    : WassMMSE.FW.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:20:24.455602+00:00
-- url     : https://prove2.me/theorems/0fe1d1be-396f-431a-8012-dd3080f4bc49
-- title:
--   Theorem 6.2, p. 24, corrected — the fully adaptive Frank-Wolfe algorithm converges linearly at rate max{1 − δ/2, 1 − (1 − √(1 − δ))²αε/(4β̄)}
-- statement:
--   **Linear convergence of the fully adaptive Frank-Wolfe algorithm.**
--
--   Let $\mathcal S=\times_{k=1}^K\mathcal S^{[k]}\subseteq\mathbb R^{d_1}\times\dots\times\mathbb R^{d_K}$ be a product of convex compact sets, let $f$ be convex on $\mathcal S$ and differentiable at its points, with optimal value $f^\star=\min_{s\in\mathcal S}f(s)$, and let $F$ be an inexact oracle with precision $\delta\in[0,1]$:
--   $$(F(s)-s)^\top\nabla f(s)\le\delta\min_{z\in\mathcal S}(z-s)^\top\nabla f(s)\qquad\forall s\in\mathcal S.$$
--   Suppose Assumption 6.1 holds:
--
--   1. $f$ is $\beta$-smooth on $\mathcal S$ for some $\beta>0$;
--   2. the marginal feasible sets are $\alpha$-strongly convex with respect to $f$ for some $\alpha>0$;
--   3. $f$ is $\varepsilon$-steep on $\mathcal S$ for some $\varepsilon>0$.
--
--   Let $(s_t,\beta_t,\eta_t)_{t\ge0}$ be a run of Algorithm 1 with inputs $s_0\in\mathcal S$, $\beta_{-1}>0$, $\tau>1$, $\zeta>1$, and let $\bar\beta=\max\{\tau\beta,\beta_{-1}\}$. Then
--
--   $$f(s_t)-f^\star\le\max\Big\{1-\frac{\delta}{2},\ 1-\frac{\big(1-\sqrt{1-\delta}\big)^2\alpha\varepsilon}{4\bar\beta}\Big\}^t\,\big(f(s_0)-f^\star\big)\qquad\forall t\ge0 .$$
--
--   The rate depends only on the oracle precision and the regularity constants, not on the unknown smoothness parameter actually used by the line search; the algorithm never needs $\beta$.
--
--   **Formalization Note** The paper prints the second term of the maximum as $1-(1-\sqrt{1-\delta})\alpha\varepsilon/(4\bar\beta)$, without the square. That version is false for $\delta\in(0,1)$: with $K=1$, $\mathcal S$ the unit disk in $\mathbb R^2$, $f(s)=s_2$ ($\beta=\alpha=\varepsilon=1$, $f^\star=-1$), $s_0=(1,0)$, $\delta=0.19$, $\tau=\zeta=2$, $\beta_{-1}=100$ (so $\bar\beta=100$) and the oracle value $F(s_0)=(-\sqrt{1-\delta^2},-\delta)$, which satisfies (6.2) with equality, the first step accepts $\beta_0=50$ and gives $f(s_1)-f^\star\approx0.999818$, above the printed bound $0.99975$ and below the corrected bound $0.999975$. The error comes from Lemma 6.3 (ii), where substituting $\theta^\star=(1-\sqrt{1-\delta})/\delta$ into (6.8) drops a square. At $\delta=1$ (exact oracle) the printed and corrected rates coincide. The statement holds for every $t\ge0$, including the trivial $t=0$. $f$ is assumed differentiable at the points of $\mathcal S$ as a function on the ambient space, and convex on $\mathcal S$ only. In (6.2) the minimum is written as "$\le\delta(z-s)^\top\nabla f(s)$ for all $z\in\mathcal S$", which is equivalent on the compact set $\mathcal S$. At $d_t=0$, where the page's stepsize is undefined, Lean's $0/0=0$ gives $\eta_t=0$.
-- source:
--   Nguyen, Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, arXiv:1911.03539v2, p. 24, Theorem 6.2 (constant corrected; see Formalization Note)

import Mathlib
import Definitions.Def_WassMMSE_FW_Setting

namespace WassMMSE.FW

open scoped RealInnerProductSpace

/-- Theorem 6.2, p. 24 (linear convergence of the fully adaptive Frank-Wolfe algorithm), **with the
corrected constant**: if Assumption 6.1 holds and `β̄ = max{τβ, β_{−1}}`, then every run of
Algorithm 1 satisfies
`f(s_t) − f⋆ ≤ max{1 − δ/2, 1 − (1 − √(1 − δ))² αε/(4β̄)}^t (f(s₀) − f⋆)` for all `t`.
The page prints `(1 − √(1 − δ))` without the square, which is false for `δ ∈ (0, 1)`; the two
agree at `δ = 1`. -/
theorem theorem_6_2
    {K : ℕ} {d : Fin K → ℕ} {S : Set (BlockSpace K d)}
    {Sk : (k : Fin K) → Set (EuclideanSpace ℝ (Fin (d k)))}
    {f : BlockSpace K d → ℝ} {F : BlockSpace K d → BlockSpace K d} {δ : ℝ}
    (hS : IsBlockFeasibleSet S Sk) (hf : IsConvexDiffObjective S f)
    (hF : IsInexactOracle S f F δ)
    {β α ε : ℝ} (hβ : IsSmoothOn S f β) (hα : IsStronglyConvexWrt S Sk f α) (hε : IsSteep S f ε)
    {fstar : ℝ} (hfstar : IsLeast (f '' S) fstar)
    {βm1 τ ζ : ℝ} {s : ℕ → BlockSpace K d} {βt ηt : ℕ → ℝ}
    (hrun : IsFAFWRun S f F βm1 τ ζ s βt ηt) :
    ∀ t : ℕ, f (s t) - fstar
      ≤ (max (1 - δ / 2) (1 - (1 - Real.sqrt (1 - δ)) ^ 2 * α * ε / (4 * max (τ * β) βm1))) ^ t
          * (f (s 0) - fstar) := by sorry

end WassMMSE.FW
