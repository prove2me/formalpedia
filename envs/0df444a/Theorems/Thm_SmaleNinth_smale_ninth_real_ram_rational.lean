-- Prove2me | Theorems.Thm_SmaleNinth_smale_ninth_real_ram_rational
-- name    : SmaleNinth.smale_ninth_real_ram_rational
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-26T02:48:51.41651+00:00
-- url     : https://prove2.me/theorems/e4e50d7e-99c4-4611-af3b-99c4dccb7de3
-- title:
--   Smale's ninth problem for rational data (real-RAM form)
-- statement:
--   There are a program $R$ of the real pointer machine and constants $C, d$ such that for all $m, n$, every rational matrix $A \in \mathbb{Q}^{m\times n}$ and every $b \in \mathbb{Q}^m$, the machine $R$ started on the memory $\mathtt{encodeLP}(A, b)$ halts within
--   $$C\,(mn+m+2)^{d}$$
--   steps and accepts exactly when $\{x \in \mathbb{R}^n : Ax \ge b\} \neq \emptyset$.
--
--   **Role.** This is `SmaleNinth.smale_ninth_real_ram` restricted to rational inputs, so it follows from the mission's real-RAM statement by specialization. Conversely it follows from OpenAI's proved rational strongly polynomial feasibility theorem `OAI.Optimization.LinearProgramming.strongly_polynomial_feasibility` (whose trace over $\mathbb{Q}$ maps to a trace over $\mathbb{R}$ under the ordered-field embedding $\mathbb{Q} \hookrightarrow \mathbb{R}$) together with the compilation theorem `SmaleNinth.real_ram_of_oai_program`. It is the common weakening that connects OpenAI's rational result to Smale's ninth problem.
-- source:
--   S. Smale, *Mathematical problems for the next century*, Math. Intelligencer 20(2):7–15, 1998, Problem 9, restricted to rational data; OpenAI, *Strongly polynomial linear programming* (preprint, Nov 2026), https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6 — Lean: OAI/Optimization/LinearProgramming/Specification.lean (StronglyPolynomialFeasibility) and Feasibility.lean

import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_BSSMachine
import Definitions.Def_SmaleNinth_RealRAM
import Mathlib.Data.Rat.Cast.Order

open Matrix LinearOptimization

theorem SmaleNinth.smale_ninth_real_ram_rational :
    ∃ (R : SmaleNinth.RAMProgram) (C d : ℕ),
      ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
        ∃ result : Bool,
          SmaleNinth.RAMDecidesInTime R
            (SmaleNinth.encodeLP (A.map ((↑) : ℚ → ℝ)) (fun i => (b i : ℝ)))
            (C * (m * n + m + 2) ^ d) result ∧
          (result = true ↔
            (polyhedron (A.map ((↑) : ℚ → ℝ)) (fun i => (b i : ℝ))).Nonempty) := by sorry
