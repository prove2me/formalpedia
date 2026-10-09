-- Prove2me | Theorems.Thm_RestartPD_Fixed_eq_32
-- name    : RestartPD.Fixed.eq_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:56:02.431578+00:00
-- url     : https://prove2.me/theorems/6b5b4724-fca8-4ebf-966e-bc2ba189f294
-- title:
--   (32), proof of Theorem 1, p. 17 — one restart contracts dist(·, Z⋆) by β inside W_R(z^{0,0})
-- statement:
--   Assume the standing assumptions of (1). Let the base algorithm satisfy Property 3 with constants $q, C$, let $\alpha > 0$ and $\beta \in (0, 1)$, and let $\{z^{n,0}\}$, $\{\bar z^{n,t}\}$ be a run of Algorithm 1 from $z^{0,0} \in Z$ with the fixed-frequency rule
--   $$t^\star = \left\lceil \frac{2C(q+2)}{\alpha\beta} \right\rceil.$$
--   Let $R = \frac{q+2}{1-\beta}\operatorname{dist}(z^{0,0}, Z^\star)$ and suppose (1) is $\alpha$-sharp on $W_R(z^{0,0})$. If both $z^{N,0}$ and $z^{N+1,0}$ lie in $W_R(z^{0,0})$, then
--   $$\operatorname{dist}(z^{N+1,0}, Z^\star) \le \beta \operatorname{dist}(z^{N,0}, Z^\star).$$
--
--   This is the contraction step of the induction in Theorem 1: sharpness at radius $\|z^{N+1,0} - z^{N,0}\|$, Property 3 and the choice of $t^\star$ combine into a factor $\beta$.
--
--   **Formalization Note** The display (32) ends with "$\le \beta^{N+1} \operatorname{dist}(z^{0,0}, Z^\star)$", which is the induction hypothesis; that last step is left to Theorem 1. Both $z^{N,0}$ and $z^{N+1,0}$ are assumed in $W_R(z^{0,0})$ because the radius used in the sharpness inequality must not exceed $\operatorname{diam}(W_R(z^{0,0}))$; the proof has both facts from the induction.
-- source:
--   Applegate, Hinder, Lu & Lubin, Faster First-Order Primal-Dual Methods for Linear Programming using Restarts and Sharpness, arXiv:2105.12715v4, p. 17, proof of Theorem 1, (32)

import Mathlib
import Definitions.Def_RestartPD_Fixed_Algorithms

namespace RestartPD.Fixed

/-- (32), proof of Theorem 1, p. 17: in a fixed-frequency restart run with
`t⋆ = ⌈2C(q + 2)/(αβ)⌉`, on a problem that is `α`-sharp on `W_R(z^{0,0})`,
`R = ((q + 2)/(1 − β)) dist(z^{0,0}, Z⋆)`, if `z^{N,0}` and `z^{N+1,0}` lie in `W_R(z^{0,0})` then
`dist(z^{N+1,0}, Z⋆) ≤ β dist(z^{N,0}, Z⋆)`. -/
theorem eq_32 {n m : ℕ} (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (hP : IsPDProblem L X Y) (p : Seminorm ℝ (E n m))
    (Runs : E n m → Set (ℕ → E n m)) (q C : ℝ) (h3 : Property3 L X Y p Runs q C)
    (α β : ℝ) (hα : 0 < α) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (z : ℕ → E n m) (zb : ℕ → ℕ → E n m) (hz0 : z 0 ∈ X ×ˢ Y)
    (hrun : IsFixedRestartRun Runs (Nat.ceil (2 * C * (q + 2) / (α * β))) z zb)
    (hsharp : IsSharpOn L X Y p α
      (Wball X Y p ((q + 2) / (1 - β) * distZ L X Y p (z 0)) (z 0)))
    (N : ℕ)
    (hN : z N ∈ Wball X Y p ((q + 2) / (1 - β) * distZ L X Y p (z 0)) (z 0))
    (hN1 : z (N + 1) ∈ Wball X Y p ((q + 2) / (1 - β) * distZ L X Y p (z 0)) (z 0)) :
    distZ L X Y p (z (N + 1)) ≤ β * distZ L X Y p (z N) := by sorry

end RestartPD.Fixed
