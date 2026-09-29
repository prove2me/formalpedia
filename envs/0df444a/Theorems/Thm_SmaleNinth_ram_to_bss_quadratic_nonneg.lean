-- Prove2me | Theorems.Thm_SmaleNinth_ram_to_bss_quadratic_nonneg
-- name    : SmaleNinth.ram_to_bss_quadratic_nonneg
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-07T18:47:37.663622+00:00
-- url     : https://prove2.me/theorems/d39e0ed7-76ac-43ee-bd5c-72d98cec273f
-- title:
--   Real RAM to tape machine: quadratic-overhead compilation
-- statement:
--   This theorem says that the random-access model and the tape model of the mission are polynomially equivalent in the direction that matters for the goal: an algorithm written for the real pointer machine can be run on the tape machine with at most quadratic slowdown.
--
--   **The assertion.** For every program $R$ of the real pointer machine there is a tape program $P$ and a constant $K$ such that, for every input $x : \mathbb{Z} \to \mathbb{R}$ vanishing on the negative cells (used as the initial memory of $R$ and as the initial tape of $P$), every $T$ and every verdict $b$: if $R$ halts with $b$ within $T$ steps, then $P$ halts with $b$ within $K\,(T+1)^2$ steps.
--
--   **Why the support condition.** The tape program keeps its registers in a fixed window of cells immediately to the left of its head, so the first register write overwrites the input cells $-1, \dots, -Z$; the simulation is therefore stated for inputs that are zero there, which includes the standard encoding `encodeLP` of a linear system (it occupies cells $0, \dots, mn+m+1$). Without such a condition a tape machine facing an input with live data in every cell has no scratch space, and a data-preserving simulation cannot even keep a loop counter.
--
--   **Why quadratic suffices.** Pointer registers of $R$ start at $0$ and change by at most one per step, apart from being set to one of the finitely many constants of the program; hence during a run of $T$ steps every pointer, and every accessed cell, lies within distance $T + K_0$ of the origin, where $K_0$ is the largest pointer constant. The tape program keeps the real registers and the pointer registers (as reals) in a fixed window of cells next to its head, together with the current position of its head; a memory access `load` or `store` is simulated by walking the head to the pointer's cell, which costs a number of shifts proportional to the distance, each shift accompanied by a fixed number of copies that slide the register window along without destroying the tape contents. Every other instruction is simulated by a constant number of tape instructions. The total is $O(T \cdot (T + K_0))$, which is $K(T+1)^2$ for a suitable $K$.
--
--   **Purpose.** Combined with a strongly polynomial algorithm in the random-access model (`SmaleNinth.smale_ninth_real_ram`), this theorem yields the goal theorem of the mission; conversely it shows that the choice of the tape machine as the mission's model costs at most a squaring of the running time relative to the model in which algorithms are normally written.
-- source:
--   Simulation of random-access machines by one-tape machines: Hopcroft-Ullman, Introduction to Automata Theory, Languages, and Computation, 1979, Section 7.6; Blum-Cucker-Shub-Smale, Complexity and Real Computation, 1998, Chapter 3 (machines over R with indirect addressing); adapted to Definitions.Def_SmaleNinth_BSSMachine and Definitions.Def_SmaleNinth_RealRAM.

import Definitions.Def_SmaleNinth_BSSMachine
import Definitions.Def_SmaleNinth_RealRAM

/-!
Compilation of the real pointer machine to the tape machine with quadratic
overhead.

Source: the standard simulation of a random-access machine by a one-tape
machine (cf. J. E. Hopcroft, J. D. Ullman, *Introduction to Automata Theory,
Languages, and Computation*, Addison-Wesley 1979, §7.6, and L. Blum,
F. Cucker, M. Shub, S. Smale, *Complexity and Real Computation*, Springer
1998, Chapter 3, on machines over `ℝ` with and without indirect addressing),
adapted to the fixed-address tape machine `Definitions.Def_SmaleNinth_BSSMachine`.
Pointers move by at most one per step, so a run of `T` steps accesses only
cells within distance `T` plus the largest pointer constant of the program;
the tape machine keeps the registers in a window of cells immediately to the
left of its head and walks to each accessed cell, costing `O(T)` per access
and `O(T²)` in total. The window initially overwrites the input cells
`-1, …, -Z`, so the input is required to vanish on negative cells (as the
standard encoding `encodeLP` does): on a tape whose every cell carries live
input a program has no scratch space at all.
-/

open Matrix

/-- **Compilation theorem.** Every program of the real pointer machine is
simulated by a tape program with quadratic overhead: if `R` halts on input
memory `x` with verdict `b` within `T` steps, the tape program `P` halts on
the tape `x` with the same verdict within `K·(T+1)²` steps, for a constant
`K` depending only on `R` — for inputs that vanish on negative cells. -/

theorem SmaleNinth.ram_to_bss_quadratic_nonneg (R : RAMProgram) :
    ∃ (P : BSSProgram) (K : ℕ), ∀ (x : ℤ → ℝ), (∀ c : ℤ, c < 0 → x c = 0) →
      ∀ (T : ℕ) (b : Bool),
        RAMDecidesInTime R x T b → BSSDecidesInTime P x (K * (T + 1) ^ 2) b := by sorry
