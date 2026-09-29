-- Prove2me | Theorems.Thm_RegularSingular_eq_zero_of_norm_le_mul_rpow_of_mul_lt
-- name    : RegularSingular.eq_zero_of_norm_le_mul_rpow_of_mul_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/ce785e8a-2d52-5566-9a74-830b8a7d7ef9
-- title:
--   Vanishing of flat solutions of a regular singular system
-- statement:
--   Let $E$ be a normed additive commutative group that is a normed space over $\mathbb{C}$, let $r, d \in \mathbb{N}$, let $M$ be an $r \times r$ matrix over $\mathbb{C}$, let $A_0,\dots,A_{d-1}$ be continuous $\mathbb{C}$-linear endomorphisms of $X = (\mathrm{Fin}\,r \to E)$ (carrying the supremum norm), and let $L \in \mathbb{R}$ be such that $\|M_{ij}\| \le L$ for all $i,j$ and $\|A_k\| \le L$ for all $k$. Let $\sigma \in \mathbb{R}$ satisfy $(r+d)L < \sigma$. Let $F, F' : \mathbb{R} \to X$ be functions such that for every $y \in (0,1]$ the function $F$ has derivative $F'(y)$ at $y$ and $$y\,F'(y) = \Big(i \mapsto \sum_{j} M_{ij}\cdot F(y)_j\Big) + \sum_{k=0}^{d-1} y^{k+1}\, A_k(F(y)),$$ the scalar multiplications being by the complex numbers $y$ and $y^{k+1}$. Let $B \in \mathbb{R}$ be such that $\|F(y)\| \le B\, y^{\sigma}$ (real power) for all $y \in (0,1]$. Then $F(y) = 0$ for every $y \in (0,1]$.
--
--   This is the crude, norm-threshold form of uniqueness for solutions of a system with a regular singular point at $y = 0$: a solution decaying faster than $y^{(r+d)L}$, where $(r+d)L$ is a crude bound for the operator norm of the coefficient $M + \sum_k y^k A_k$ on $E^r$, must vanish identically on $(0,1]$. It is used in the sharp version [`RegularSingular.eq_zero_of_norm_le_mul_rpow_of_forall_isRoot_re_lt`](thm.html#RegularSingular.eq_zero_of_norm_le_mul_rpow_of_forall_isRoot_re_lt), where the threshold is the largest real part of a root of the indicial polynomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RegularSingular_eq_zero_of_norm_le_mul_rpow_of_mul_lt.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Instances.Matrix

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem RegularSingular.eq_zero_of_norm_le_mul_rpow_of_mul_lt
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (r d : ℕ)
    (M : Matrix (Fin r) (Fin r) ℂ) (A : Fin d → ((Fin r → E) →L[ℂ] (Fin r → E))) (L : ℝ)
    (hM : ∀ i j, ‖M i j‖ ≤ L) (hA : ∀ k, ‖A k‖ ≤ L)
    (σ : ℝ) (hσ : (r + d) * L < σ)
    (F F' : ℝ → (Fin r → E))
    (hF : ∀ y ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt F (F' y) y ∧
      (y : ℂ) • F' y = (fun i => ∑ j, M i j • F y j) + ∑ k : Fin d, ((y : ℂ) ^ ((k : ℕ) + 1)) • A k (F y))
    (B : ℝ) (hB : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F y‖ ≤ B * y ^ σ) :
    ∀ y ∈ Set.Ioc (0 : ℝ) 1, F y = 0 := by sorry
