-- Prove2me | Theorems.Thm_SmaleNinth_real_ram_decides_one_variable_lp_linear
-- name    : SmaleNinth.real_ram_decides_one_variable_lp_linear
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T01:19:39.809977+00:00
-- url     : https://prove2.me/theorems/ce5fafd8-1195-4cb1-a5c7-bf20e896479f
-- title:
--   Model sanity, real RAM: one-variable LP in linear time
-- statement:
--   On the real pointer machine of `Definitions.Def_SmaleNinth_RealRAM` (real registers, integer pointer registers, a memory indexed by $\mathbb{Z}$, unit cost per instruction, indirect addressing through pointers), one-variable linear programming feasibility is decidable in **linear** time.
--
--   Precisely: there are a single program $R$ and a constant $C$ such that for every $m$, every $A \in \mathbb{R}^{m \times 1}$ and every $b \in \mathbb{R}^m$, the machine started with memory `encodeLP A b` halts within $C\,(m+1)$ steps, and it accepts exactly when the system $a_i x \ge b_i$, $i < m$, has a solution $x \in \mathbb{R}$.
--
--   The algorithm is the obvious sweep: maintain the running lower bound $L = \max\{b_i/a_i : a_i > 0\}$, the running upper bound $R = \min\{b_i/a_i : a_i < 0\}$, presence flags for the two, and a flag recording whether some constraint with $a_i = 0$ and $b_i > 0$ has been seen; the system is feasible iff no such constraint occurs and $L \le R$ whenever both bounds are present. Each constraint costs $O(1)$ instructions because the coefficient $a_i$ and the right-hand side $b_i$ are reached through two pointers that are incremented once per step.
--
--   This is the exact counterpart, in the random-access model, of the milestone statement `SmaleNinth.bss_decides_one_variable_lp`, which is **false** in the fixed-address tape model: there the two halves of a constraint sit $m$ cells apart and a crossing-sequence argument forces $\Omega(m^2)$ steps (`SmaleNinth.bss_one_variable_lp_no_linear_program`). Together the two statements separate the two machine models at linear time and show that the quadratic overhead of the compiler `SmaleNinth.ram_to_bss_quadratic_nonneg` is not an artifact of the construction.
-- source:
--   Sweep algorithm for one-dimensional linear programming; cf. N. Megiddo, Linear-time algorithms for linear programming in R^3 and related problems, SIAM J. Comput. 12 (1983) 759-776 (case n = 1), on the unit-cost real random-access machine of Definitions.Def_SmaleNinth_RealRAM with the encodeLP input convention of Definitions.Def_SmaleNinth_BSSMachine.

import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_BSSMachine
import Definitions.Def_SmaleNinth_RealRAM

/-!
Model sanity for the random-access model of `Definitions.Def_SmaleNinth_RealRAM`:
one-variable LP feasibility is decided in linear time by a uniform program of
the real pointer machine, on the same input encoding `encodeLP` used for the
tape machine.

Source: the standard sweep algorithm for one-dimensional linear programming
(maintain the running interval of feasible values, cf. N. Megiddo, *Linear-time
algorithms for linear programming in R^3 and related problems*, SIAM J.
Comput. 12 (1983) 759-776, the trivial case n = 1), implemented on a unit-cost
real random-access machine with indirect addressing.
-/

open Matrix LinearOptimization

/-- **Model sanity, random-access form: one-variable LP in linear time.**
There is a uniform program of the real pointer machine deciding, for every
`m` and every one-variable system `a_i x >= b_i`, its feasibility within
`C*(m+1)` steps on the standard input encoding. -/

theorem SmaleNinth.real_ram_decides_one_variable_lp_linear :
    ∃ (R : RAMProgram) (C : ℕ),
      ∀ (m : ℕ) (A : Matrix (Fin m) (Fin 1) ℝ) (b : Fin m → ℝ),
        ∃ result : Bool,
          RAMDecidesInTime R (encodeLP A b) (C * (m + 1)) result ∧
          (result = true ↔ (polyhedron A b).Nonempty) := by sorry
