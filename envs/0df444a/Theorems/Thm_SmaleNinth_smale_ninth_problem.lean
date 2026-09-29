-- Prove2me | Theorems.Thm_SmaleNinth_smale_ninth_problem
-- name    : SmaleNinth.smale_ninth_problem
-- status  : Open
-- author  : @ORdos
-- created : 2026-09-06T15:25:33.999759+00:00
-- url     : https://prove2.me/theorems/8bf5478b-14fe-468e-85c5-1ce842fbd1e4
-- title:
--   Smale's 9th problem: polynomial-time LP feasibility over $\mathbb{R}$
-- statement:
--   Consider the decision problem: given a matrix $A \in \mathbb{R}^{m\times n}$ and a vector $b \in \mathbb{R}^m$ of **arbitrary real numbers**, decide whether the system of linear inequalities has a solution, that is, whether
--
--   $$\{\,x \in \mathbb{R}^n \;\mid\; Ax \ge b\,\} \;\ne\; \emptyset ,$$
--
--   where the inequality is componentwise. The instance is presented to a machine over the real numbers as $mn + m + 2$ tape cells (the two dimensions, the entries of $A$ in row-major order, then $b$), and the cost of a computation is the number of instructions it executes, each arithmetic operation, comparison and shift costing one unit regardless of the magnitude of the reals involved.
--
--   **The assertion.** There exist a single program $P$, and constants $C, d \in \mathbb{N}$, such that for every $m$, every $n$, every $A \in \mathbb{R}^{m\times n}$ and every $b \in \mathbb{R}^m$, the program $P$ started on the encoded instance halts with the correct verdict within
--
--   $$C\,(mn + m + 2)^{d}$$
--
--   steps: it accepts if $\{x \mid Ax \ge b\}$ is nonempty, and rejects otherwise.
--
--   **Reading the quantifiers.** The program and both constants are chosen once, before any instance is seen; only the verdict and the actual halting time depend on the instance. The algorithm is therefore required to be **uniform** — one finite instruction list for all dimensions — and its running time to be bounded by a fixed polynomial in the number of input reals. In particular the bound may not depend on the magnitudes, the bit lengths, or any conditioning of $A$ and $b$; every algorithm currently known for this problem violates exactly this, its iteration count being governed by a quantity that is unbounded over real instances of fixed dimension.
--
--   **What the statement deliberately leaves unfixed.** Neither the degree $d$, nor the constant $C$, nor any structure of the program is prescribed: the claim is only that *some* polynomial bound holds, so it is invariant under future quantitative improvements and cannot be invalidated by a sharper analysis. Conversely, an algorithm is here a finite program in the fixed instruction set, not an arbitrary function of the input reals — a set-theoretic decision function always exists, and would make the statement vacuous.
--
--   This is Problem 9 on Smale's list of mathematical problems for the next century, and it is **open**.
-- source:
--   S. Smale, Mathematical problems for the next century, Mathematical Intelligencer 20(2):7-15, 1998, Problem 9 (also in: Mathematics: Frontiers and Perspectives, AMS 2000). Machine model: Blum-Shub-Smale, Bull. AMS 21(1):1-46, 1989.

import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_BSSMachine

/-!
Smale's 9th problem: polynomial-time linear programming feasibility over
the real numbers.

Source: S. Smale, *Mathematical problems for the next century*, Mathematical
Intelligencer 20(2):7–15, 1998, Problem 9: "Is there a polynomial-time
algorithm over the real numbers which decides the feasibility of the linear
system of inequalities $Ax \ge b$?" — in the machine model of Blum–Shub–
Smale (Bull. AMS 21(1):1–46, 1989), formalized in
`Definitions.Def_SmaleNinth_BSSMachine`.

The statement asks for a single BSS program `P` (one uniform algorithm, with
arbitrary real machine constants) and constants `C, d` such that on every
instance — every `m`, `n`, every real `A : m × n` and `b : m` — the program,
run on the standard input encoding, halts within `C·(mn + m + 2)^d` steps
(unit cost per arithmetic operation, comparison, or shift; `mn + m + 2` is
the number of input cells) and accepts exactly when `{x | Ax ≥ b}` is
nonempty.
-/

open LinearOptimization

/-- **Smale's 9th problem** (Smale 1998, Problem 9; Blum–Shub–Smale model).
There is a uniform BSS program over `ℝ` deciding the feasibility of
`Ax ≥ b` in a number of steps polynomial in the number `mn + m + 2` of
input reals. -/

theorem SmaleNinth.smale_ninth_problem :
    ∃ (P : BSSProgram) (C d : ℕ),
      ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
        ∃ result : Bool,
          BSSDecidesInTime P (encodeLP A b) (C * (m * n + m + 2) ^ d) result ∧
          (result = true ↔ (polyhedron A b).Nonempty) := by sorry
