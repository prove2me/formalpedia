-- Prove2me | Theorems.Thm_TruncNewton_Global_theorem_2_1
-- name    : TruncNewton.Global.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:24:50.429318+00:00
-- url     : https://prove2.me/theorems/b9846e24-10cd-4636-834c-f548b898a7df
-- title:
--   Theorem 2.1 — global convergence of TNCG iterates
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be twice continuously differentiable and have bounded sublevel sets. Fix $\varepsilon>0$, any forcing sequence $\eta_k$, $0<\alpha<1/2$, and $\alpha<\beta<1$. From every starting point $x_0$ there exists a full TNCG run. Every such run satisfies
--
--   $$\lim_{k\to\infty}\|\nabla f(x_k)\|=0.$$
--
--   If $x^*$ is a limit point of its iterates and $H(x^*)$ is positive definite, then the entire sequence converges to that point:
--
--   $$x_k\longrightarrow x^*.$$
--
--   This is the paper's main global convergence assertion, with “well defined” expressed by existence of a run from every initial point.
--
--   **Formalization Note** The norm is Euclidean, $H$ is the derivative of the gradient, and the run uses positive step lengths and the first TNCG exit. No nonnegative forcing-value or step-size upper-bound assumption is added.
-- source:
--   Dembo and Steihaug, Truncated-Newton algorithms for large-scale unconstrained optimization, Math. Programming 26 (1983), p. 195, Theorem 2.1, https://doi.org/10.1007/BF02592055

import Mathlib
import Definitions.Def_TruncNewton_Global_Setting

namespace TruncNewton.Global

theorem theorem_2_1 {n : ℕ} (f : E n → ℝ) (hf : ContDiff ℝ 2 f)
    (hL : ∀ x0 : E n, Bornology.IsBounded {x | f x ≤ f x0})
    (ε : ℝ) (hε : 0 < ε) (η : ℕ → ℝ) (α β : ℝ)
    (hα : 0 < α) (hα2 : α < 1 / 2) (hαβ : α < β) (hβ1 : β < 1) :
    (∀ x0 : E n, ∃ x : ℕ → E n, ∃ lam : ℕ → ℝ, ∃ p : ℕ → E n,
      IsTNCGRun f ε η α β x0 x lam p) ∧
    ∀ (x0 : E n) (x : ℕ → E n) (lam : ℕ → ℝ) (p : ℕ → E n),
      IsTNCGRun f ε η α β x0 x lam p →
        Filter.Tendsto (fun k => ‖gradient f (x k)‖) Filter.atTop (nhds 0) ∧
        ∀ xstar : E n, MapClusterPt xstar Filter.atTop x →
          (∀ v : E n, v ≠ 0 → 0 < inner ℝ v (hess f xstar v)) →
          Filter.Tendsto x Filter.atTop (nhds xstar) := by sorry

end TruncNewton.Global
