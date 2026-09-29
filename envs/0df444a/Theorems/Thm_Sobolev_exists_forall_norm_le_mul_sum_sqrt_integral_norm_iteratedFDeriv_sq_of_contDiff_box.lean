-- Prove2me | Theorems.Thm_Sobolev_exists_forall_norm_le_mul_sum_sqrt_integral_norm_iteratedFDeriv_sq_of_contDiff_box
-- name    : Sobolev.exists_forall_norm_le_mul_sum_sqrt_integral_norm_iteratedFDeriv_sq_of_contDiff_box
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/b52a189b-c7be-562a-b7b5-f0c202dd7e75
-- title:
--   Sobolev bound on a cube: sup norm by L² derivatives
-- statement:
--   Fix $n \in \mathbb{N}$ and a real $\ell$ with $0 < \ell$. The assertion is the existence of a real constant $c$, depending only on $n$ and $\ell$, with $0 \le c$ and with the following uniform property: for every $a : \mathrm{Fin}\,n \to \mathbb{R}$, every function $f$ from $\mathrm{Fin}\,n \to \mathbb{R}$ (with its sup norm) to $\mathbb{C}$ that is of class $C^{n}$ over $\mathbb{R}$, and every point $x$ with $x_i \in [a_i, a_i + \ell]$ for all $i$, one has $$\|f(x)\| \le c \sum_{k=0}^{n} \left(\int_{Q} \bigl\|D^{k} f(y)\bigr\|^{2}\,dy\right)^{1/2},$$ where $Q = \prod_{i} [a_i, a_i + \ell]$ is the closed cube of side $\ell$ with corner $a$, the integral is the Bochner integral against the Lebesgue (volume) measure on $\mathrm{Fin}\,n \to \mathbb{R}$ restricted to $Q$, $D^{k} f(y)$ denotes the $k$-th iterated Fréchet derivative of $f$ at $y$ with its norm as a $k$-multilinear map, and the square root is `Real.sqrt`. The constant is independent of $a$, of $f$ and of $x$; the number of derivatives used equals the dimension $n$.
--
--   This is the elementary Sobolev embedding $W^{n,2}(Q) \subset C^{0}(Q)$ on a cube of fixed side length, in the form in which the sup norm of a $C^{n}$ function on the cube is controlled by the $L^{2}$ norms of its derivatives of order at most $n$, with a constant uniform in the position of the cube. It serves as the local analytic input for sup-norm bounds on automorphic forms, being cited by [`AutomorphicForm.exists_isCompact_forall_norm_le_mul_of_forall_eLpNorm_foldr_archDeriv_le`](thm.html#AutomorphicForm.exists_isCompact_forall_norm_le_mul_of_forall_eLpNorm_foldr_archDeriv_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Sobolev_exists_forall_norm_le_mul_sum_sqrt_integral_norm_iteratedFDeriv_sq_of_contDiff_box.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem Sobolev.exists_forall_norm_le_mul_sum_sqrt_integral_norm_iteratedFDeriv_sq_of_contDiff_box
    (n : ℕ) (ℓ : ℝ) (hℓ : 0 < ℓ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (a : Fin n → ℝ) (f : (Fin n → ℝ) → ℂ), ContDiff ℝ n f →
      ∀ x : Fin n → ℝ, (∀ i, x i ∈ Set.Icc (a i) (a i + ℓ)) →
        ‖f x‖ ≤ c * ∑ k ∈ Finset.range (n + 1),
          Real.sqrt (∫ y in Set.pi Set.univ (fun i => Set.Icc (a i) (a i + ℓ)), ‖iteratedFDeriv ℝ k f y‖ ^ 2) := by sorry
