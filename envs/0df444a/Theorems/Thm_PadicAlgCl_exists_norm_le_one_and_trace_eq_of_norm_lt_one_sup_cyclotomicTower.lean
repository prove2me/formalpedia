-- Prove2me | Theorems.Thm_PadicAlgCl_exists_norm_le_one_and_trace_eq_of_norm_lt_one_sup_cyclotomicTower
-- name    : PadicAlgCl.exists_norm_le_one_and_trace_eq_of_norm_lt_one_sup_cyclotomicTower
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/2d663c02-3bc0-578d-9837-b5fbc1804367
-- title:
--   Tate: trace surjectivity onto 𝔪 in the cyclotomic tower
-- statement:
--   Let $p$ be a prime and let $\overline{\mathbb Q}_p$ be the algebraic closure `PadicAlgCl p` of $\mathbb Q_p$, carrying the absolute value extending the $p$-adic one. Let $K$ be an intermediate field of $\overline{\mathbb Q}_p/\mathbb Q_p$ that is finite-dimensional over $\mathbb Q_p$, and for each $n$ let [`PadicAlgCl.cyclotomicTower p n`](def/PadicAlgCl_CyclotomicTower.html#L9) be the subfield of $\overline{\mathbb Q}_p$ generated over $\mathbb Q_p$ by the set of $\zeta$ with $\zeta^{p^n}=1$; write $K_\infty = K \sqcup \bigsqcup_n \mathrm{cyclotomicTower}\,p\,n$ for the join of $K$ with all these cyclotomic levels, i.e. $K(\mu_{p^\infty})$. Let $L$ be an intermediate field of $\overline{\mathbb Q}_p/K_\infty$ which is finite-dimensional over $K_\infty$, and let $x \in K_\infty$ satisfy $\|x\| < 1$ for the absolute value of $\overline{\mathbb Q}_p$. The assertion is that there exists $y \in L$ with $\|y\| \le 1$ and $\mathrm{Tr}_{L/K_\infty}(y) = x$, the trace being the $K_\infty$-algebra trace of the finite extension $L/K_\infty$. Equivalently, $\mathrm{Tr}_{L/K_\infty}(\mathcal O_L)$ contains the maximal ideal $\{x \in K_\infty : \|x\| < 1\}$ of the valuation ring of $K_\infty$.
--
--   This is Tate's trace-surjectivity statement for the cyclotomic tower, expressing that $K(\mu_{p^\infty})$ is deeply ramified (almost étale) over $K$: the trace from the valuation ring of any finite extension covers the maximal ideal. It follows by combining a general criterion in terms of bounds on the trace dual with the asymptotic bound on trace duals along the levels $K \sqcup \mathbb Q_p(\mu_{p^n})$, and is used in the construction of a coboundary for continuous cocycles of the Galois group fixing $K(\mu_{p^\infty})$ acting on the $p$-adic complex numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicAlgCl_exists_norm_le_one_and_trace_eq_of_norm_lt_one_sup_cyclotomicTower.lean

import Mathlib
import Definitions.Def_PadicAlgCl_CyclotomicTower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicAlgCl.exists_norm_le_one_and_trace_eq_of_norm_lt_one_sup_cyclotomicTower
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (L : IntermediateField ↥(K ⊔ ⨆ n : ℕ, PadicAlgCl.cyclotomicTower p n) (PadicAlgCl p))
    [FiniteDimensional ↥(K ⊔ ⨆ n : ℕ, PadicAlgCl.cyclotomicTower p n) L]
    (x : ↥(K ⊔ ⨆ n : ℕ, PadicAlgCl.cyclotomicTower p n)) (hx : ‖(x : PadicAlgCl p)‖ < 1) :
    ∃ y : L, ‖(y : PadicAlgCl p)‖ ≤ 1 ∧
      Algebra.trace ↥(K ⊔ ⨆ n : ℕ, PadicAlgCl.cyclotomicTower p n) L y = x := by sorry
