-- Prove2me | Theorems.Thm_TalagrandConc_LinearSuprema_eq_8_1_2
-- name    : TalagrandConc.LinearSuprema.eq_8_1_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:47:23.542308+00:00
-- url     : https://prove2.me/theorems/252fac96-ea51-42ab-8140-40290f6dd574
-- title:
--   Eq. (8.1.2) — convex distance controls a linear supremum
-- statement:
--   Let $\mathcal F$ be a nonempty family of real $N$-tuples with finite, positive
--   $\sigma=\sup_{\alpha\in\mathcal F}\|\alpha\|_2$, and let $r=(r_i)$. On $[0,1]^N$ set
--   $Z(x)=\sup_{\alpha\in\mathcal F}\sum_i\alpha_i(r_i+x_i)$ and
--   $A(a)=\{y\in[0,1]^N:Z(y)\le a\}$. For every real $a$ and $x\in[0,1]^N$,
--   $$Z(x)\le a+\sigma f_c(A(a),x).$$
--
--   This is the deterministic observation relating the supremum to the convex-hull distance.
--
--   **Formalization Note** The inequality uses extended nonnegative arithmetic for the positive
--   part of $Z(x)-a$. This is equivalent to the displayed inequality when $f_c$ is finite and
--   remains meaningful when $A(a)$ is empty.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 156, Eq. (8.1.2)

import Mathlib
import Definitions.Def_TalagrandConc_LinearSuprema_Basic

namespace TalagrandConc.LinearSuprema

theorem eq_8_1_2 {N : ℕ} (F : Set (Fin N → ℝ))
    (hF : F.Nonempty) (hσfinite : BddAbove (coeffNorm '' F))
    (hσ : 0 < sigma F) (r x : Fin N → ℝ) (a : ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    ENNReal.ofReal (linearSupremum F (fun i => r i + x i) - a) ≤
      ENNReal.ofReal (sigma F) * convexDistance (linearSublevel F r a) x := by sorry

end TalagrandConc.LinearSuprema
