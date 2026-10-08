-- Prove2me | Theorems.Thm_PalmQueueing_Ordering_majorization_bounds
-- name    : PalmQueueing.Ordering.majorization_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T02:22:20.448116+00:00
-- url     : https://prove2.me/theorems/cf753b0a-81e7-4158-8c88-b73152625062
-- title:
--   Lemma 4.1.2 — the identity and the reversal bracket every reordering
-- statement:
--   **Lemma 4.1.2.** Let $x_1 \le \dots \le x_n$ and $y_1 \le \dots \le y_n$ be real numbers.
--   Then, for all $\gamma \in \Gamma$,
--   $$ (y - x) \prec (y_\gamma - x) \prec (y_- - x) , \tag{4.1.17} $$
--   where $y_-$ is defined by $y_- = (y_n, \dots, y_1)$.
--
--   The two extremes of the majorization order over all reorderings are the **identity**, which pairs
--   the two sequences in the same order, and the **reversal**, which pairs them oppositely; every other
--   matching lies between. Lemma 4.1.1 supplies the step, and this is what iterating it gives.
--
--   This is the combinatorial heart of the FIFO optimality proof. Under a discipline $\phi$, customer
--   $k$ receives service $\sigma_{\gamma(k)}$ for some permutation $\gamma$, and FIFO is $\gamma =
--   \mathrm{id}$; the waiting time vectors then satisfy
--   $V(A',\psi) = (\mathbf{B}(A',\psi) - \mathbf{T}) \prec (\mathbf{B}(A,\phi) - \mathbf{T}) =
--   V(A,\phi)$ (4.1.21), and since convex symmetric functions are Schur-convex, $E^0[f(V_\psi)] \le
--   E^0[f(V_\phi)]$ for every convex $f$.
--
--   Both inequalities are stated: the lower bound is the one Property 4.1.3 uses, the upper says which
--   discipline is worst.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 267, Lemma 4.1.2

import Mathlib
import Definitions.Def_PalmQueueing_Ordering_PartialOrders

/-!
# Lemma 4.1.2: the identity and the reversal bracket every reordering (§4.1.3, p.267)
-/

namespace PalmQueueing.Ordering

/-- **Lemma 4.1.2** (p.267). Let `x₁ ≤ x₂ ≤ … ≤ xₙ` and `y₁ ≤ y₂ ≤ … ≤ yₙ` be real numbers. Then,
for all `γ ∈ Γ`,

`(4.1.17)  (y − x) ≺ (y_γ − x) ≺ (y₋ − x)`,

where `y₋` is defined by `y₋ = (yₙ, …, y₁)`.

The two extremes of the majorization order over all reorderings are the **identity**, which pairs
the two sequences in the same order, and the **reversal**, which pairs them oppositely. Every
other matching lies between. Lemma 4.1.1 supplies the step; this is what iterating it gives.

This is the combinatorial heart of the FIFO optimality proof. Under a discipline `φ`, customer `k`
receives service `σ_{γ(k)}` for some permutation `γ`; FIFO is the case `γ = id`. The waiting time
vectors then satisfy `V(A', ψ) ≺ V(A, φ)` (4.1.21), and since a convex symmetric function is
Schur-convex, `E⁰[f(V_ψ)] ≤ E⁰[f(V_φ)]` for every convex `f` — Property 4.1.3.

Both inequalities of (4.1.17) are stated. The lower bound is the one Property 4.1.3 uses; the upper
says which discipline is worst. -/
theorem majorization_bounds {n : ℕ} (x y : Fin n → ℝ)
    (hx : Monotone x) (hy : Monotone y) (g : Equiv.Perm (Fin n)) :
    Majorized (fun k => y k - x k) (fun k => y (g k) - x k) ∧
    Majorized (fun k => y (g k) - x k) (fun k => reverseVec y k - x k) := by sorry

end PalmQueueing.Ordering
