-- Prove2me | Theorems.Thm_RegularSingular_eq_zero_of_norm_le_mul_rpow_of_forall_isRoot_re_lt
-- name    : RegularSingular.eq_zero_of_norm_le_mul_rpow_of_forall_isRoot_re_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/d0b11e2b-94f9-557b-a042-f61ec438d77f
-- title:
--   Flat solutions of a regular singular system vanish
-- statement:
--   Let $E$ be a complex Banach space, let $r,d$ be natural numbers, let $M$ be an $r\times r$ complex matrix, and let $A_0,\dots,A_{d-1}$ be continuous $\mathbb{C}$-linear endomorphisms of $X=E^{r}$ (functions $\mathrm{Fin}\,r\to E$). Let $q$ be a nonzero polynomial in $\mathbb{C}[T]$ annihilating $M$, i.e. $q(M)=0$ under the evaluation of $q$ at $M$ in the matrix algebra, and let $\sigma$ be a real number such that every root $e$ of $q$ satisfies $\operatorname{Re} e<\sigma$. Let $F,F':(0,1]\to X$ (given as functions on all of $\mathbb{R}$) be such that for every $y\in(0,1]$ the function $F$ has derivative $F'(y)$ at $y$ and
--   $$y\,F'(y)=\Big(i\mapsto \sum_{j} M_{ij}\,F(y)_j\Big)+\sum_{k=0}^{d-1} y^{k+1}\,A_k\big(F(y)\big),$$
--   the scalars $y$ and $y^{k+1}$ acting through the inclusion $\mathbb{R}\subset\mathbb{C}$. Assume further that there is a real number $B$ with $\|F(y)\|\le B\,y^{\sigma}$ for all $y\in(0,1]$. The conclusion is that $F(y)=0$ for every $y\in(0,1]$.
--
--   This is the Frobenius-type uniqueness statement at a regular singular point: the indicial exponents of the system are eigenvalues of $M$, hence roots of $q$, so a solution decaying faster than $y^{\sigma}$ with $\sigma$ beyond all of them must vanish identically. The proof reduces to the small-coefficient case [`RegularSingular.eq_zero_of_norm_le_mul_rpow_of_mul_lt`](thm.html#RegularSingular.eq_zero_of_norm_le_mul_rpow_of_mul_lt), where the threshold is expressed by a bound $(r+d)L<\sigma$ on the norms of $M$ and the $A_k$; it is used in the analytic estimates of the cubic induction step of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RegularSingular_eq_zero_of_norm_le_mul_rpow_of_forall_isRoot_re_lt.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Instances.Matrix

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem RegularSingular.eq_zero_of_norm_le_mul_rpow_of_forall_isRoot_re_lt
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (r d : ℕ)
    (M : Matrix (Fin r) (Fin r) ℂ) (A : Fin d → ((Fin r → E) →L[ℂ] (Fin r → E)))
    (q : Polynomial ℂ) (hq : q ≠ 0) (hqM : Polynomial.aeval M q = 0)
    (σ : ℝ) (hσ : ∀ e : ℂ, q.IsRoot e → e.re < σ)
    (F F' : ℝ → (Fin r → E))
    (hF : ∀ y ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt F (F' y) y ∧
      (y : ℂ) • F' y = (fun i => ∑ j, M i j • F y j) + ∑ k : Fin d, ((y : ℂ) ^ ((k : ℕ) + 1)) • A k (F y))
    (B : ℝ) (hB : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F y‖ ≤ B * y ^ σ) :
    ∀ y ∈ Set.Ioc (0 : ℝ) 1, F y = 0 := by sorry
