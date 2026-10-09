-- Prove2me | Theorems.Thm_RestartPD_Adaptive_theorem_2
-- name    : RestartPD.Adaptive.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:45:07.236393+00:00
-- url     : https://prove2.me/theorems/a4bab954-a759-4f83-bc4f-9fd856fe4ba3
-- title:
--   Theorem 2 — adaptive restart lengths and linear convergence
-- statement:
--   Let $L$ define a differentiable convex–concave primal–dual problem on closed convex $X\times Y$ with a nonempty saddle set $Z^\star$, and use a seminorm $\|\cdot\|_p$. Suppose the base algorithm satisfies Property 3 with constants $q,C>0$. Starting from a feasible $z^{0,0}$, run Algorithm 1 with the adaptive condition (30), a user-chosen positive first interval $\tau^0$, and $\beta\in(0,1)$. Suppose $\alpha>0$ and there is a set $S\subseteq X\times Y$ containing every outer start $z^{k,0}$ on which the problem is $\alpha$-sharp. Put
--   $$
--   t^\star=\left\lceil\frac{2C(q+2)}{\alpha\beta}\right\rceil.
--   $$
--   Then, for every outer index $k\ge1$, both conclusions hold:
--   $$
--   \tau^k\le t^\star,\qquad
--   \operatorname{dist}_p(z^{k,0},Z^\star)
--     \le \beta^k\frac{t^\star}{\tau^0}
--     \operatorname{dist}_p(z^{0,0},Z^\star).
--   $$
--
--   The first bound limits the work in every adaptive interval after the first, and the second gives geometric decay of the distance to saddle points.
--
--   **Formalization Note** The run records the first positive trigger of (30) at each $k\ge1$. The bound excludes $k=0$, since $\tau^0$ is freely selected. The paper's feasible-region and finite-value assumptions are represented by the stronger explicit condition $Z^\star\ne\varnothing$, ensuring distance is well defined as a real infimum. The normalized gap and diameter are extended-real valued, retaining unbounded cases. The $\tau^0$ quotient is a real quotient.
-- source:
--   Applegate, Hinder, Lu & Lubin, Faster First-Order Primal-Dual Methods for Linear Programming using Restarts and Sharpness, arXiv:2105.12715v4, p. 18, Theorem 2(i)–(ii), (33)

import Mathlib
import Definitions.Def_RestartPD_Adaptive_Restarts

namespace RestartPD.Adaptive

/-- Theorem 2, p. 18: adaptive restart lengths and distance decay. -/
theorem theorem_2 {n m : ℕ}
    (L : RestartPD.Fixed.Primal n → RestartPD.Fixed.Dual m → ℝ) (X : Set (RestartPD.Fixed.Primal n))
    (Y : Set (RestartPD.Fixed.Dual m)) (hP : RestartPD.Fixed.IsPDProblem L X Y)
    (p : Seminorm ℝ (RestartPD.Fixed.E n m)) (Runs : RestartPD.Fixed.E n m → Set (ℕ → RestartPD.Fixed.E n m))
    (q C : ℝ) (h3 : RestartPD.Fixed.Property3 L X Y p Runs q C)
    (α β : ℝ) (hα : 0 < α) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (τ : ℕ → ℕ) (z : ℕ → RestartPD.Fixed.E n m) (zb : ℕ → ℕ → RestartPD.Fixed.E n m)
    (hz0 : z 0 ∈ X ×ˢ Y)
    (hrun : IsAdaptiveRestartRun L X Y p Runs β τ z zb)
    (S : Set (RestartPD.Fixed.E n m)) (hzS : ∀ k, z k ∈ S)
    (hsharp : RestartPD.Fixed.IsSharpOn L X Y p α S) :
    let tstar := Nat.ceil (2 * C * (q + 2) / (α * β))
    ∀ k : ℕ, 1 ≤ k →
      τ k ≤ tstar ∧
        RestartPD.Fixed.distZ L X Y p (z k) ≤
          β ^ k * ((tstar : ℝ) / (τ 0 : ℝ)) * RestartPD.Fixed.distZ L X Y p (z 0) := by sorry

end RestartPD.Adaptive
