-- Prove2me | Theorems.Thm_TruncNewton_Global_descent_quotient_tendsto_zero
-- name    : TruncNewton.Global.descent_quotient_tendsto_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:09:24.95556+00:00
-- url     : https://prove2.me/theorems/b8200e03-3247-470d-88fe-d638f770acde
-- title:
--   Proof of Theorem A.3 — normalized directional derivative tends to zero
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be twice continuously differentiable with bounded sublevel sets, let $\varepsilon>0$, and take $0<\alpha<1/2$ and $\alpha<\beta<1$. For any TNCG run with directions $p_k$ and iterates $x_k$,
--
--   $$\lim_{k\to\infty}\frac{\langle\nabla f(x_k),p_k\rangle}{\|p_k\|}=0.$$
--
--   This is the Zoutendijk-type limit quoted in the paper's proof of global convergence.
--
--   **Formalization Note** When $p_k=0$, the quotient takes Lean's value zero; the first-exit rule permits this only at a stationary iterate. The forcing values are unrestricted, as in Theorem 2.1.
-- source:
--   Dembo and Steihaug, Truncated-Newton algorithms for large-scale unconstrained optimization, Math. Programming 26 (1983), p. 208, proof of Theorem A.3, https://doi.org/10.1007/BF02592055

import Mathlib
import Definitions.Def_TruncNewton_Global_Setting

namespace TruncNewton.Global

theorem descent_quotient_tendsto_zero {n : ℕ} (f : E n → ℝ) (hf : ContDiff ℝ 2 f)
    (hL : ∀ x0 : E n, Bornology.IsBounded {x | f x ≤ f x0})
    (ε : ℝ) (hε : 0 < ε) (η : ℕ → ℝ) (α β : ℝ)
    (hα : 0 < α) (hα2 : α < 1 / 2) (hαβ : α < β) (hβ1 : β < 1)
    (x0 : E n) (x : ℕ → E n) (lam : ℕ → ℝ) (p : ℕ → E n)
    (hrun : IsTNCGRun f ε η α β x0 x lam p) :
    Filter.Tendsto (fun k => inner ℝ (gradient f (x k)) (p k) / ‖p k‖)
      Filter.atTop (nhds 0) := by sorry

end TruncNewton.Global
