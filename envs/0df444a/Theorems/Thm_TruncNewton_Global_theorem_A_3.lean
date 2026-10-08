-- Prove2me | Theorems.Thm_TruncNewton_Global_theorem_A_3
-- name    : TruncNewton.Global.theorem_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:15:58.315075+00:00
-- url     : https://prove2.me/theorems/b97a875a-dddd-4294-8cc2-bd941e90a10c
-- title:
--   Theorem A.3 — well-defined TNCG iterates and vanishing gradient
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be twice continuously differentiable with bounded sublevel sets. Fix $\varepsilon>0$, any forcing sequence $\eta_k$, $0<\alpha<1/2$, and $\alpha<\beta<1$. From every initial point $x_0$ there is a full TNCG run, and every such run satisfies
--
--   $$\lim_{k\to\infty}\|\nabla f(x_k)\|=0.$$
--
--   This is the first part of Theorem 2.1: the minor iteration and line search remain defined, and the gradient norm decays on every resulting sequence.
--
--   **Formalization Note** The existence clause gives the paper's “well defined” assertion mathematical content; the result is not merely conditional on an existing run.
-- source:
--   Dembo and Steihaug, Truncated-Newton algorithms for large-scale unconstrained optimization, Math. Programming 26 (1983), pp. 207–208, Theorem A.3, https://doi.org/10.1007/BF02592055

import Mathlib
import Definitions.Def_TruncNewton_Global_Setting

namespace TruncNewton.Global

theorem theorem_A_3 {n : ℕ} (f : E n → ℝ) (hf : ContDiff ℝ 2 f)
    (hL : ∀ x0 : E n, Bornology.IsBounded {x | f x ≤ f x0})
    (ε : ℝ) (hε : 0 < ε) (η : ℕ → ℝ) (α β : ℝ)
    (hα : 0 < α) (hα2 : α < 1 / 2) (hαβ : α < β) (hβ1 : β < 1) :
    (∀ x0 : E n, ∃ x : ℕ → E n, ∃ lam : ℕ → ℝ, ∃ p : ℕ → E n,
      IsTNCGRun f ε η α β x0 x lam p) ∧
    ∀ (x0 : E n) (x : ℕ → E n) (lam : ℕ → ℝ) (p : ℕ → E n),
      IsTNCGRun f ε η α β x0 x lam p →
        Filter.Tendsto (fun k => ‖gradient f (x k)‖) Filter.atTop (nhds 0) := by sorry

end TruncNewton.Global
