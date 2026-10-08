-- Prove2me | Theorems.Thm_TruncNewton_Global_theorem_A_4
-- name    : TruncNewton.Global.theorem_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:16:14.14927+00:00
-- url     : https://prove2.me/theorems/991d8892-748e-4b51-b100-883558bc26e3
-- title:
--   Theorem A.4 — eventual admissibility of the unit step
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be twice continuously differentiable, and suppose $x_k\to x^*$, $\nabla f(x^*)=0$, and the Hessian at $x^*$ is positive definite. Let every $p_k$ be a strict descent direction and suppose
--
--   $$\frac{\langle p_k,\nabla f(x_k)+H(x_k)p_k\rangle}{\langle p_k,p_k\rangle}\longrightarrow0.$$
--
--   For $0<\alpha<1/2$ and $\alpha<\beta<1$, the unit step eventually satisfies sufficient decrease (1.9) and gradient curvature (1.10). If $\beta>1/2$, it also satisfies the alternative function-value condition (1.11).
--
--   This local result identifies when the line search may take a full Newton-like step.
--
--   **Formalization Note** The printed theorem omits $\nabla f(x^*)=0$, although its proof uses it. Without it the claim fails, for example for $f(x)=x+x^2/2+x^4$, $x_k=0$, $p_k=-1$. The paper applies the result only after establishing vanishing gradients. The line-search parameters retain the ranges given in (1.9)–(1.11).
-- source:
--   Dembo and Steihaug, Truncated-Newton algorithms for large-scale unconstrained optimization, Math. Programming 26 (1983), pp. 208–209, Theorem A.4, (A.12), https://doi.org/10.1007/BF02592055

import Mathlib
import Definitions.Def_TruncNewton_Global_Setting

namespace TruncNewton.Global

theorem theorem_A_4 {n : ℕ} (f : E n → ℝ) (hf : ContDiff ℝ 2 f)
    (x p : ℕ → E n) (xstar : E n)
    (hx : Filter.Tendsto x Filter.atTop (nhds xstar))
    (hpd : ∀ v : E n, v ≠ 0 → 0 < inner ℝ v (hess f xstar v))
    (hg0 : gradient f xstar = 0)
    (hdesc : ∀ k, inner ℝ (gradient f (x k)) (p k) < 0)
    (hA12 : Filter.Tendsto
      (fun k => inner ℝ (p k) (gradient f (x k) + hess f (x k) (p k)) /
        inner ℝ (p k) (p k)) Filter.atTop (nhds 0))
    (α β : ℝ) (hα : 0 < α) (hα2 : α < 1 / 2)
    (hαβ : α < β) (hβ1 : β < 1) :
    ∃ k0 : ℕ, ∀ k ≥ k0,
      cond19 f α (x k) (p k) 1 ∧ cond110 f β (x k) (p k) 1 ∧
      (1 / 2 < β → cond111 f β (x k) (p k) 1) := by sorry

end TruncNewton.Global
