-- Prove2me | Theorems.Thm_PadicAlgCl_exists_norm_le_one_and_trace_eq_of_forall_traceDual_norm_le
-- name    : PadicAlgCl.exists_norm_le_one_and_trace_eq_of_forall_traceDual_norm_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/eb76f265-d784-547d-b733-69a2bc104f07
-- title:
--   Trace surjectivity from a bound on the codifferent
-- statement:
--   Let $p$ be a prime and let $\overline{\mathbb{Q}}_p$ denote `PadicAlgCl p`, an algebraic closure of $\mathbb{Q}_p$ with its absolute value $\|\cdot\|$. Let $F$ be an intermediate field of $\overline{\mathbb{Q}}_p/\mathbb{Q}_p$ that is finite-dimensional over $\mathbb{Q}_p$, and let $E$ be an intermediate field of $\overline{\mathbb{Q}}_p/F$ that is finite-dimensional over $F$. Let $r$ be a real number subject to the following hypothesis: for every $z \in E$ such that $\|\operatorname{Tr}_{E/F}(zw)\| \le 1$ holds for all $w \in E$ with $\|w\| \le 1$, one has $\|z\| \le r$; that is, every element of the codifferent of $E/F$ (computed with respect to the unit ball of $E$, using `Algebra.trace F E` and measuring norms after embedding into $\overline{\mathbb{Q}}_p$) has absolute value at most $r$. Then for every $x \in F$ with $\|x\| \le r^{-1}$ there exists $y \in E$ with $\|y\| \le 1$ and $\operatorname{Tr}_{E/F}(y) = x$, the equality being one of elements of $F$.
--
--   This is the classical comparison between the image of the ring of integers under the trace and the different of a finite extension of local fields, stated here in the quantitative form that a bound $r$ on the codifferent of $E/F$ forces every $x \in F$ with $\|x\| \le r^{-1}$ to be the trace of an element of the unit ball of $E$. It is used in the almost-étale estimates for the cyclotomic tower, via [`PadicAlgCl.exists_norm_le_one_and_trace_eq_of_norm_lt_one_sup_cyclotomicTower`](thm.html#PadicAlgCl.exists_norm_le_one_and_trace_eq_of_norm_lt_one_sup_cyclotomicTower).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicAlgCl_exists_norm_le_one_and_trace_eq_of_forall_traceDual_norm_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicAlgCl.exists_norm_le_one_and_trace_eq_of_forall_traceDual_norm_le
    (p : ℕ) [Fact p.Prime] (F : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] F]
    (E : IntermediateField F (PadicAlgCl p)) [FiniteDimensional F E] (r : ℝ)
    (hE : ∀ z : E, (∀ w : E, ‖(w : PadicAlgCl p)‖ ≤ 1 →
        ‖((Algebra.trace F E (z * w) : F) : PadicAlgCl p)‖ ≤ 1) → ‖(z : PadicAlgCl p)‖ ≤ r)
    (x : F) (hx : ‖(x : PadicAlgCl p)‖ ≤ r⁻¹) :
    ∃ y : E, ‖(y : PadicAlgCl p)‖ ≤ 1 ∧ Algebra.trace F E y = x := by sorry
