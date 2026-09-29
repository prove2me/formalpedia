-- Prove2me | Theorems.Thm_SmaleNinth_smale_ninth_real_ram
-- name    : SmaleNinth.smale_ninth_real_ram
-- status  : Open
-- author  : @Zexuan Liu
-- created : 2026-09-07T18:42:30.032978+00:00
-- url     : https://prove2.me/theorems/f75ee086-7c08-483c-aadb-aa27473645ae
-- title:
--   Smale's ninth problem, real-RAM form (open)
-- statement:
--   This is the mission's goal theorem transposed to the random-access model in which algorithms for linear programming are normally written. It is an **open problem**: it is Smale's ninth problem itself, up to the polynomial equivalence of the two machine models.
--
--   **The assertion.** There exist a single program $R$ of the real pointer machine (finitely many real registers with exact arithmetic, finitely many integer pointers with increment, decrement, copy, set and compare, and a random-access memory) and constants $C, d \in \mathbb{N}$ such that for every $m$, $n$, $A \in \mathbb{R}^{m \times n}$ and $b \in \mathbb{R}^m$, the program started with the standard encoding of the instance in memory (cells $0, 1$ hold $m$ and $n$, then $A$ row-major, then $b$) halts within
--
--   $$C\,(mn + m + 2)^d$$
--
--   steps and accepts if and only if $\{x \in \mathbb{R}^n \mid Ax \ge b\}$ is nonempty.
--
--   **Reading the quantifiers.** The program and the constants are fixed before any instance is seen; only the verdict and the actual running time depend on the instance. The bound may depend on the dimensions only, not on the magnitudes, bit lengths or conditioning of the data, which is exactly what makes the question hard: every known polynomial-time method has an iteration count controlled by such a data-dependent quantity.
--
--   **Relation to the goal.** By the compilation theorem `SmaleNinth.ram_to_bss_quadratic`, a program $R$ with budget $C N^d$ ($N = mn+m+2$) yields a tape program with budget $K(CN^d+1)^2 \le 4K(C+1)^2 N^{2d}$, so this statement implies the goal theorem `SmaleNinth.smale_ninth_problem`. It is offered so that contributors can work in the random-access model without tape bookkeeping.
--
--   **Status (2026).** Strongly polynomial algorithms are known for combinatorial LPs (Tardos 1986) and for linear programs with at most two nonzero entries per row or per column (Dadush, Koh, Natura, Olver, Végh, STOC 2024); no self-concordant-barrier interior-point method can be strongly polynomial (Allamigeon, Gaubert, Vandame, STOC 2022). A 2025 arXiv preprint (arXiv:2503.12041) claims a strongly polynomial algorithm for general LP; it has not been peer-reviewed or independently confirmed and is not treated here as establishing the statement.
-- source:
--   S. Smale, Mathematical problems for the next century, Math. Intelligencer 20(2):7-15, 1998, Problem 9 (real-RAM reading); status: Dadush, Koh, Natura, Olver, Vegh, A strongly polynomial algorithm for linear programs with at most two nonzero entries per row or column, STOC 2024 (special case); Allamigeon, Gaubert, Vandame, No self-concordant barrier interior point method is strongly polynomial, STOC 2022 (barrier); general case open as of 2026.

import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_BSSMachine
import Definitions.Def_SmaleNinth_RealRAM

/-!
Smale's ninth problem in the random-access formulation: a uniform program of
the real pointer machine decides `{x | Ax ≥ b} ≠ ∅` within a number of steps
polynomial in the number of input reals.

Source: S. Smale, *Mathematical problems for the next century*, Math.
Intelligencer 20(2):7–15, 1998, Problem 9, in the real-RAM reading of the
question; the input convention is `encodeLP` of
`Definitions.Def_SmaleNinth_BSSMachine`, read here as the initial memory of
the pointer machine. **Open problem.** As of 2026 the strongest peer-reviewed
results are strongly polynomial algorithms for special classes (Tardos 1986;
Dadush–Koh–Natura–Olver–Végh, STOC 2024, for at most two nonzeros per row or
column); a 2025 arXiv preprint claims a general algorithm but has not been
peer-reviewed or independently confirmed.
-/

open Matrix LinearOptimization

/-- **Smale's ninth problem, real-RAM form.** There is a program `R` of the
real pointer machine and constants `C, d` such that `R` decides the
feasibility of every system `Ax ≥ b` within `C·(mn+m+2)^d` steps. -/

theorem SmaleNinth.smale_ninth_real_ram :
    ∃ (R : RAMProgram) (C d : ℕ),
      ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
        ∃ result : Bool,
          RAMDecidesInTime R (encodeLP A b) (C * (m * n + m + 2) ^ d) result ∧
          (result = true ↔ (polyhedron A b).Nonempty) := by sorry
