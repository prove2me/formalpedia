-- Prove2me | Theorems.Thm_RestartPD_Fixed_thm1_partial_sum
-- name    : RestartPD.Fixed.thm1_partial_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:48.540006+00:00
-- url     : https://prove2.me/theorems/839b2655-a4ef-436c-81e9-03db05982794
-- title:
--   Proof of Theorem 1, first display, p. 17 — if (31) holds for n ≤ N then z^{N+1,0} ∈ W_R(z^{0,0})
-- statement:
--   Let the base algorithm satisfy Property 3 with constants $q, C$, let $\beta \in (0, 1)$, let $t^\star \ge 1$, and let $\{z^{n,0}\}$, $\{\bar z^{n,t}\}$ be a run of Algorithm 1 restarting every $t^\star$ inner steps from $z^{0,0} \in Z$. If for some $N$
--   $$\operatorname{dist}(z^{n,0}, Z^\star) \le \beta^n \operatorname{dist}(z^{0,0}, Z^\star) \quad (0 \le n \le N),$$
--   then
--   $$\|z^{N+1,0} - z^{0,0}\| \le \frac{q + 2}{1 - \beta} \operatorname{dist}(z^{0,0}, Z^\star),$$
--   and therefore $z^{N+1,0} \in W_R(z^{0,0})$ with $R = \frac{q+2}{1-\beta}\operatorname{dist}(z^{0,0}, Z^\star)$.
--
--   This is the step of the induction in Theorem 1 that keeps the outer iterates inside the set on which sharpness is assumed.
--
--   **Formalization Note** The restart length is any $t^\star \ge 1$; this step does not use its value. The standing assumptions of (1) are not needed and not assumed.
-- source:
--   Applegate, Hinder, Lu & Lubin, Faster First-Order Primal-Dual Methods for Linear Programming using Restarts and Sharpness, arXiv:2105.12715v4, p. 17, proof of Theorem 1, first display

import Mathlib
import Definitions.Def_RestartPD_Fixed_Algorithms

namespace RestartPD.Fixed

/-- Proof of Theorem 1, first display, p. 17: in a fixed-frequency restart run, if (31) holds for
all `n ≤ N`, then `‖z^{N+1,0} − z^{0,0}‖ ≤ ((q + 2)/(1 − β)) dist(z^{0,0}, Z⋆)`, i.e.
`z^{N+1,0} ∈ W_R(z^{0,0})`. -/
theorem thm1_partial_sum {n m : ℕ} (L : Primal n → Dual m → ℝ) (X : Set (Primal n))
    (Y : Set (Dual m)) (p : Seminorm ℝ (E n m))
    (Runs : E n m → Set (ℕ → E n m)) (q C : ℝ) (h3 : Property3 L X Y p Runs q C)
    (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (tstar : ℕ) (htstar : 1 ≤ tstar)
    (z : ℕ → E n m) (zb : ℕ → ℕ → E n m) (hz0 : z 0 ∈ X ×ˢ Y)
    (hrun : IsFixedRestartRun Runs tstar z zb)
    (N : ℕ) (hind : ∀ k ≤ N, distZ L X Y p (z k) ≤ β ^ k * distZ L X Y p (z 0)) :
    p (z (N + 1) - z 0) ≤ (q + 2) / (1 - β) * distZ L X Y p (z 0) ∧
      z (N + 1) ∈ Wball X Y p ((q + 2) / (1 - β) * distZ L X Y p (z 0)) (z 0) := by sorry

end RestartPD.Fixed
