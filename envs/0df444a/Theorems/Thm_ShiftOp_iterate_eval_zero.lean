-- Prove2me | Theorems.Thm_ShiftOp_iterate_eval_zero
-- name    : ShiftOp.iterate_eval_zero
-- status  : Proved
-- author  : @milia
-- created : 2026-11-13T03:01:51.045213+00:00
-- url     : https://prove2.me/theorems/860bcdbb-72ce-4ae8-bf81-2dc8c9a109db
-- title:
--   Shift-operator identity for powers of a linear form
-- statement:
--   Let $R$ be a commutative semiring, $\sigma$ a finite set of variables, $r \ge 0$, and $c : \sigma^r \to R$. Consider the constant-coefficient differential operator
--   $$D = \sum_{t \in \sigma^r} c(t)\,\frac{\partial}{\partial v_{t_1}}\cdots\frac{\partial}{\partial v_{t_r}}$$
--   with symbol $g(w) = \sum_t c(t)\,w_{t_1}\cdots w_{t_r}$. For $w \in R^\sigma$ write $w\cdot v = \sum_l w_l v_l$. Then for all $m, E \ge 0$,
--   $$\Bigl[D^{m}\,(w\cdot v)^{E}\Bigr]_{v=0} = \begin{cases} (mr)!\; g(w)^{m}, & E = mr,\\ 0, & \text{otherwise.}\end{cases}$$
--
--   This is the shift identity behind the Morozov–Shakirov recursion. Applied to $(v\cdot p)^{rm}$, the operator $g(\partial_v)^m/(rm)!$ evaluated at $v = 0$ returns $g(p)^m$. This converts sums of powers of a linear form into sums of powers of an arbitrary form of degree $r$.
--
--   **Formalization Note** The operator is iterated with `Nat.iterate`; the word derivative is `(List.ofFn t).foldr (fun j q => MvPolynomial.pderiv j q)`.
-- source:
--   Morozov and Shakirov, Analogue of the identity Log Det = Trace Log for resultants, arXiv:0804.4632v3, Section 3, identity (15).

import Mathlib

namespace ShiftOp

theorem iterate_eval_zero {σ R : Type*} [Fintype σ] [CommSemiring R]
    (r : ℕ) (c : (Fin r → σ) → R) (w : σ → R) (m E : ℕ) :
    MvPolynomial.eval 0
      ((fun p : MvPolynomial σ R =>
          ∑ t : Fin r → σ, c t • (List.ofFn t).foldr (fun j q => MvPolynomial.pderiv j q) p)^[m]
        ((∑ i, MvPolynomial.C (w i) * MvPolynomial.X i) ^ E)) =
      if E = m * r then
        ((m * r).factorial : R) * (∑ t : Fin r → σ, c t * ∏ s, w (t s)) ^ m
      else 0 := by sorry

end ShiftOp
