-- Prove2me | Theorems.Thm_SmaleNinth_no_linear_ram_to_bss_compiler
-- name    : SmaleNinth.no_linear_ram_to_bss_compiler
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T01:23:17.834033+00:00
-- url     : https://prove2.me/theorems/fa1c9b2a-80b9-4ee5-9f6c-260647388970
-- title:
--   No linear-overhead compilation of the pointer machine into the tape machine
-- statement:
--   The real pointer machine of `Definitions.Def_SmaleNinth_RealRAM` cannot be simulated by the fixed-address tape machine of `Definitions.Def_SmaleNinth_BSSMachine` with only a constant-factor loss of time.
--
--   Precisely, there is no assignment $R \mapsto (P_R, K_R)$ of a tape program and a constant to every pointer-machine program such that, whenever $R$ decides an input $x$ (vanishing on the negative cells, so that the tape machine has scratch space) with answer $b$ within $T$ steps, $P_R$ decides the same input with the same answer within $K_R (T+1)$ steps.
--
--   The counterexample is one-variable linear programming feasibility. On the pointer machine it is decided in $O(m)$ steps, because the coefficient $a_i$ and the right-hand side $b_i$ of a constraint are reached through two independently incremented pointers (`SmaleNinth.real_ram_decides_one_variable_lp_linear`). On the tape machine no program decides it in $O(m)$ steps: in the encoding `encodeLP` the two halves of a constraint sit $m$ cells apart, and a crossing-sequence argument over $\mathbb{R}$ forbids the linear budget (`SmaleNinth.bss_one_variable_lp_no_linear_program`). A linear-overhead compiler applied to the first program would produce a tape program of the forbidden kind.
--
--   The statement is the exact sharpness counterpart of `SmaleNinth.ram_to_bss_quadratic_nonneg`, which achieves overhead $K(T+1)^2$: the quadratic loss there is a genuine feature of the two models, not a defect of that construction. It also justifies stating Smale's ninth problem in the random-access form `SmaleNinth.smale_ninth_real_ram`, since the two models are provably not interchangeable at the level of constant-factor time.
-- source:
--   Consequence of SmaleNinth.real_ram_decides_one_variable_lp_linear and SmaleNinth.bss_one_variable_lp_no_linear_program; the lower bound is a crossing-sequence argument in the style of F. C. Hennie, One-tape, off-line Turing machine computations, Information and Control 8 (1965) 553-578, adapted to real-number machines.

import Definitions.Def_SmaleNinth_BSSMachine
import Definitions.Def_SmaleNinth_RealRAM

/-!
Sharpness of the compilation of the real pointer machine into the tape
machine: the quadratic overhead of `SmaleNinth.ram_to_bss_quadratic_nonneg`
cannot be lowered to a linear one.

Source: consequence of the linear-time random-access algorithm
`SmaleNinth.real_ram_decides_one_variable_lp_linear` and the linear-time tape
lower bound `SmaleNinth.bss_one_variable_lp_no_linear_program`; the latter is
a crossing-sequence argument in the style of F. C. Hennie, *One-tape,
off-line Turing machine computations*, Information and Control 8 (1965)
553-578.
-/

/-- **No compilation with linear overhead.** There is no way to translate
every pointer-machine program into a tape program whose running time is
bounded by a constant multiple of the pointer machine's. -/

theorem SmaleNinth.no_linear_ram_to_bss_compiler :
    ¬ ∀ (R : RAMProgram), ∃ (P : BSSProgram) (K : ℕ), ∀ (x : ℤ → ℝ), (∀ c : ℤ, c < 0 → x c = 0) →
        ∀ (T : ℕ) (b : Bool),
          RAMDecidesInTime R x T b → BSSDecidesInTime P x (K * (T + 1)) b := by sorry
