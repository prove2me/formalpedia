-- Prove2me | Theorems.Thm_SmaleNinth_integer_polyhedron_solution_bound
-- name    : SmaleNinth.integer_polyhedron_solution_bound
-- status  : Proved
-- author  : @ORdos
-- created : 2026-09-06T15:26:10.18185+00:00
-- url     : https://prove2.me/theorems/f0b63176-59d2-4453-a542-1b29d8d5d969
-- title:
--   Cramer–Hadamard solution bound for integer systems
-- statement:
--   A feasible system of linear inequalities with integer coefficients cannot have all its solutions astronomically far from the origin: feasibility already forces a solution of controlled size, with a bound depending only on the number of variables and the size of the coefficients.
--
--   **The assertion.** Let $U \ge 1$ be an integer, let $A \in \mathbb{Z}^{m\times n}$ and $b \in \mathbb{Z}^m$ satisfy $|A_{ij}| \le U$ for all $i, j$ and $|b_i| \le U$ for all $i$, and suppose the system has at least one real solution. Then it has a real solution $x$ with
--
--   $$|x_j| \;\le\; n!\;U^{\,n} \qquad \text{for every } j = 0, \dots, n-1 .$$
--
--   **What the bound does and does not involve.** It is a bound on each coordinate, hence on the sup-norm, and it depends only on the number $n$ of variables and the coefficient bound $U$ — the number $m$ of inequalities does not appear, however large it is. The solution produced is real; no rationality or integrality of $x$ is claimed, and none holds in general. Both $A$ and $b$ are bounded by the same $U$, and $U \ge 1$ is required, so the hypotheses never force the data to vanish.
--
--   **Why it matters here.** This is the step that converts a geometric question into a question of bounded size. A feasible integer system is guaranteed to meet an explicit box $[-n!U^n,\, n!U^n]^n$, so a search may be confined to that box, and the resulting volumes and radii are described by numbers whose logarithms are polynomial in $n$ and $\log U$. Every polynomial-time algorithm for linear feasibility in the bit model rests on an estimate of this kind, and it is the first place where the magnitude of the data enters the complexity — which is precisely what the real-number formulation of the problem forbids.
--
--   **Sharpness.** The constant $n!\,U^n$ is the classical generous one and is not claimed to be optimal; only its logarithm's polynomial growth is used downstream, so any sharpening is a strengthening of this statement rather than a correction to it.
-- source:
--   Classical; B. Korte, J. Vygen, Combinatorial Optimization, 6th ed., Springer, Section 4.1 (Size of Vertices and Faces); Bertsimas-Tsitsiklis, Introduction to Linear Optimization, Section 8.4; A. Schrijver, Theory of Linear and Integer Programming, Wiley 1986, Chapter 10. Stated with the generous bound n! U^n.

import Definitions.Def_Polyhedron

/-!
The Cramer–Hadamard bound: a nonempty linear system with integer data has a
solution of explicitly bounded size.

Source: the classical size estimate underlying Khachiyan's theorem —
B. Korte, J. Vygen, *Combinatorial Optimization*, 6th ed., Springer, §4.1
(Size of Vertices and Faces), and Bertsimas–Tsitsiklis, *Introduction to
Linear Optimization*, §8.4; cf. A. Schrijver, *Theory of Linear and Integer
Programming*, Wiley 1986, Chapter 10. A point of a minimal face of
`{x | Ax ≥ b}` solves a nonsingular integer subsystem, so by Cramer's rule
and the crude expansion bound `|det| ≤ r!·Uʳ` on `r × r` integer matrices
with entries bounded by `U` (and `|det| ≥ 1` for a nonsingular integer
matrix), its components are bounded by `n!·Uⁿ`.

The bound `n!·Uⁿ` is the generous classical one; only its polynomial bit
size matters downstream.
-/

open Matrix LinearOptimization

/-- **Cramer–Hadamard solution bound** (Korte–Vygen §4.1;
Bertsimas–Tsitsiklis §8.4). If the system `Ax ≥ b` with integer entries
bounded by `U ≥ 1` has a real solution, it has one with every component
bounded by `n!·Uⁿ`. -/

theorem SmaleNinth.integer_polyhedron_solution_bound {m n : ℕ} (U : ℕ) (hU : 1 ≤ U)
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ))
    (hne : (polyhedron (A.map (Int.cast : ℤ → ℝ))
      (fun i => (b i : ℝ))).Nonempty) :
    ∃ x ∈ polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)),
      ∀ j, |x j| ≤ (n.factorial : ℝ) * (U : ℝ) ^ n := by sorry
