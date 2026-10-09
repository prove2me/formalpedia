-- Prove2me | Theorems.Thm_RestartPD_Adaptive_prop_8
-- name    : RestartPD.Adaptive.prop_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:46:15.560182+00:00
-- url     : https://prove2.me/theorems/d4333bfc-d0d4-4ba2-8903-4d45a4b94cf1
-- title:
--   Proposition 8 — zero seminorm displacement yields a saddle point
-- statement:
--   Suppose a primal–dual algorithm satisfies Property 3 with constants $q,C>0$. Start from a feasible point $z^0$ and consider one of its admissible averaged output sequences $\bar z^t$. For any $t\ge1$, if $\|\bar z^t-z^0\|_p=0$, then
--   $$
--   \bar z^t\in Z^\star.
--   $$
--
--   This handles the zero-radius case excluded from the positive-radius sharpness inequality.
--
--   **Formalization Note** The paper also prints $\bar z^t=z^0$. Equality does not follow for a seminorm with a nontrivial kernel, so this item states the saddle-point membership used in the paper's proof.
-- source:
--   Applegate, Hinder, Lu & Lubin, Faster First-Order Primal-Dual Methods for Linear Programming using Restarts and Sharpness, arXiv:2105.12715v4, p. 17, Proposition 8

import Mathlib
import Definitions.Def_RestartPD_Adaptive_Restarts

namespace RestartPD.Adaptive

/-- Proposition 8, p. 17: zero semi-norm displacement gives a saddle point.
The printed equality of the two points is not asserted for a general semi-norm. -/
theorem prop_8 {n m : ℕ} (L : RestartPD.Fixed.Primal n → RestartPD.Fixed.Dual m → ℝ)
    (X : Set (RestartPD.Fixed.Primal n)) (Y : Set (RestartPD.Fixed.Dual m))
    (hP : RestartPD.Fixed.IsPDProblem L X Y) (p : Seminorm ℝ (RestartPD.Fixed.E n m))
    (Runs : RestartPD.Fixed.E n m → Set (ℕ → RestartPD.Fixed.E n m)) (q C : ℝ)
    (h3 : RestartPD.Fixed.Property3 L X Y p Runs q C)
    (z0 : RestartPD.Fixed.E n m) (hz0 : z0 ∈ X ×ˢ Y)
    (zb : ℕ → RestartPD.Fixed.E n m) (hzb : zb ∈ Runs z0)
    (t : ℕ) (ht : 1 ≤ t) (hzero : p (zb t - z0) = 0) :
    zb t ∈ RestartPD.Fixed.Zstar L X Y := by sorry

end RestartPD.Adaptive
