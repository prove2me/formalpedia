-- Prove2me | Theorems.Thm_TruncNewton_Global_wolfe_step_exists
-- name    : TruncNewton.Global.wolfe_step_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:09:08.802604+00:00
-- url     : https://prove2.me/theorems/ba9ed0ea-4d2c-409a-ab44-088d84fd87b4
-- title:
--   Proof of Theorem A.3 — a Wolfe step exists
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be twice continuously differentiable with bounded sublevel sets. Choose $0<\alpha<1/2$ and $\alpha<\beta<1$. At any $x$ and along any strict descent direction $p$, there is a positive step length $t$ satisfying both line-search conditions:
--
--   $$f(x+tp)\le f(x)+\alpha t\langle \nabla f(x),p\rangle,\qquad \langle\nabla f(x+tp),p\rangle\ge\beta\langle\nabla f(x),p\rangle.$$
--
--   This existence statement supplies the major step once the minor iteration has found a descent direction.
-- source:
--   Dembo and Steihaug, Truncated-Newton algorithms for large-scale unconstrained optimization, Math. Programming 26 (1983), pp. 207–208, proof of Theorem A.3 and (1.9)–(1.10), https://doi.org/10.1007/BF02592055

import Mathlib
import Definitions.Def_TruncNewton_Global_Setting

namespace TruncNewton.Global

theorem wolfe_step_exists {n : ℕ} (f : E n → ℝ) (hf : ContDiff ℝ 2 f)
    (hL : ∀ x0 : E n, Bornology.IsBounded {x | f x ≤ f x0})
    (α β : ℝ) (hα : 0 < α) (hα2 : α < 1 / 2) (hαβ : α < β) (hβ1 : β < 1) :
    ∀ x p : E n, inner ℝ (gradient f x) p < 0 →
      ∃ t : ℝ, 0 < t ∧ cond19 f α x p t ∧ cond110 f β x p t := by sorry

end TruncNewton.Global
