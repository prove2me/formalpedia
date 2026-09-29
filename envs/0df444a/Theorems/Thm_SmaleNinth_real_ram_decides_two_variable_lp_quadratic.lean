-- Prove2me | Theorems.Thm_SmaleNinth_real_ram_decides_two_variable_lp_quadratic
-- name    : SmaleNinth.real_ram_decides_two_variable_lp_quadratic
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T02:23:54.337041+00:00
-- url     : https://prove2.me/theorems/c3508284-d6cd-4bd9-b702-96953759c797
-- title:
--   Two-variable LP in quadratic time on the real RAM
-- statement:
--   There are a single program $R$ of the real pointer machine of `Definitions.Def_SmaleNinth_RealRAM` and a constant $C$ such that, for every $m$, every $A \in \mathbb{R}^{m\times 2}$ and every $b \in \mathbb{R}^m$, the machine started with memory `encodeLP A b` halts within $C(m+1)^2$ steps and accepts exactly when the system $a_i x + b_i y \ge c_i$, $i < m$, has a solution in $\mathbb{R}^2$.
--
--   The algorithm is Fourier–Motzkin elimination fused with the one-variable sweep. Eliminating the second variable replaces the system by a one-variable system consisting of the rows with vanishing second coefficient together with one combined row for each pair of rows whose second coefficients have opposite signs. Rather than materialising that system, whose size is quadratic, the program runs a double loop over all ordered pairs of rows and feeds each derived constraint directly into the running interval $[L, R]$ maintained by the one-variable procedure, together with the presence flags and the infeasibility flag. Pairs that produce no constraint are fed the vacuous inequality $0 \ge 0$, so every pass performs the same bounded amount of work.
--
--   This is the case $n = 2$ of fixed-dimension linear programming. Megiddo and Dyer showed that for each fixed number of variables the problem is solvable in time linear in the number of constraints, by prune-and-search; the bound above is the weaker quadratic one that the naive elimination gives, and it is stated on the same machine model and input convention as the mission's goal, so the two are directly comparable. Together with the one-variable result it makes the first two rungs of the fixed-dimension ladder available in the model in which Smale's ninth problem is posed here.
--
--   *Formalization note.* The program has 90 instructions. The correctness proof separates the machine-independent part — the abstract state, its update along one constraint, and the correctness of the verdict, reused from the one-variable development — from the machine part, where a reachability calculus with one lemma per instruction is used to verify the initialisation, the row-reading and case analysis that computes the constraint fed at each pair, the update block, the two nested loops, and the final decision.
-- source:
--   Fourier-Motzkin elimination of one variable combined with the one-variable sweep; the case n = 2 of N. Megiddo, Linear programming in linear time when the dimension is fixed, J. ACM 31 (1984) 114-127, and M. E. Dyer, Linear time algorithms for two- and three-variable linear programs, SIAM J. Comput. 13 (1984) 31-45, with the quadratic bound of the naive elimination. Machine model: Definitions.Def_SmaleNinth_RealRAM; input convention encodeLP of Definitions.Def_SmaleNinth_BSSMachine.

import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_BSSMachine
import Definitions.Def_SmaleNinth_RealRAM

/-!
Two-variable linear programming on the real pointer machine: a uniform program
decides the feasibility of a two-variable system of `m` inequalities within
`C (m+1)^2` steps, on the standard input encoding `encodeLP`.

Source: elimination of one variable (Fourier-Motzkin) followed by the
one-variable sweep; this is the case `n = 2` of the fixed-dimension results of
N. Megiddo, *Linear programming in linear time when the dimension is fixed*,
J. ACM 31 (1984) 114-127, and M. E. Dyer, *Linear time algorithms for
two- and three-variable linear programs*, SIAM J. Comput. 13 (1984) 31-45,
with the quadratic bound of the naive elimination rather than their linear one.
-/

open Matrix LinearOptimization

/-- **Two-variable LP feasibility in quadratic time on the pointer machine.** -/

theorem SmaleNinth.real_ram_decides_two_variable_lp_quadratic :
    ∃ (R : RAMProgram) (C : ℕ),
      ∀ (m : ℕ) (A : Matrix (Fin m) (Fin 2) ℝ) (b : Fin m → ℝ),
        ∃ result : Bool,
          RAMDecidesInTime R (encodeLP A b) (C * (m + 1) ^ 2) result ∧
          (result = true ↔ (polyhedron A b).Nonempty) := by sorry
