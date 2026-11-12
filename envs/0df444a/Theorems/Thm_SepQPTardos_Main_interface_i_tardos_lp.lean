-- Prove2me | Theorems.Thm_SepQPTardos_Main_interface_i_tardos_lp
-- name    : SepQPTardos.Main.interface_i_tardos_lp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:15:03.975455+00:00
-- url     : https://prove2.me/theorems/ca618b13-5938-4422-a7a1-783bd8b7ee37
-- title:
--   §2 interface (i) — Tardos: LPs with an integer constraint matrix in poly(dimensions, ⟨D⟩) operations
-- statement:
--   Consider linear programs
--   $$\min\ c^\top x\quad\text{subject to}\quad D_1x=d_1,\ \ D_2x\le d_2,\ \ x_j\ge0\ (j\in S),\ \ x_j\ \text{free}\ (j\notin S),$$
--   where $D_1\in\mathbb Z^{p_1\times n}$ and $D_2\in\mathbb Z^{p_2\times n}$ are integer matrices and $d_1,d_2,c$ are rational. There is one admissible program of the real RAM and constants $C,k,C',k'$ such that on every such LP the program halts within
--   $$C\,(p_1+p_2+n+\langle D_1\rangle+\langle D_2\rangle+2)^k$$
--   steps — a bound independent of the right-hand sides $d_1,d_2$ and the objective $c$ — and outputs correctly one of: an optimal primal–dual pair (primal feasible $x$, dual feasible $(y_1,y_2)$, complementary slackness), a Farkas certificate of infeasibility, or a feasible point together with a ray of negative cost. Every number in every register and memory cell during the run is a rational of encoding length at most $C'(L+2)^{k'}$, where $L$ is the complete input length.
--
--   This is Tardos's theorem in the form used throughout the paper: the feasibility, boundedness, recovery and certificate LPs all have constraint matrices built from $A$, $A^\top$ and unit coefficients.
--
--   Differences from the source:
--   - generalization: counts basic operations (addition, subtraction, multiplication, division, comparison) → counts every executed instruction of the real RAM, pointer and control instructions included; reason: a bound on all instructions implies the same bound on the arithmetic operations
--   - reading: an LP can be solved exactly; in the feasible finite case an optimal primal–dual pair → the program outputs an optimal primal–dual pair, a Farkas certificate of infeasibility, or a feasible point with a negative-cost ray; reason: §2.2 (p. 5) uses the Farkas certificate of an LP solved this way; this is the stronger reading
--   - encoding: LPs with an integer constraint matrix, variable bounds and free variables → min cᵀx s.t. D₁x = d₁, D₂x ≤ d₂, x_S ≥ 0, other variables free, D₁, D₂ integer; reason: every LP of the paper (feasibility, (5), (15), (18), (25), (26)) has this form with integer rows from A, Aᵀ and unit coefficients
--   - encoding: poly(dimensions, ⟨D⟩) operations; polynomial intermediate encodings → C·(p₁ + p₂ + n + ⟨D₁⟩ + ⟨D₂⟩ + 2)^k steps and C'·(L + 2)^k' bits, constants fixed before the instance; reason: standard meaning of a polynomial bound uniform over all inputs
--   - encoding: binary encoding length, convention not fixed → ⟨z⟩ = 1 + size|z| for integers, ⟨p/q⟩ = ⟨p⟩ + size q in lowest terms, sums over entries; reason: all standard conventions agree up to polynomial factors
--   - encoding: rational arithmetic model, an algorithm → one admissible program (integer constants only) of the published real RAM SmaleNinth.RAMProgram with fixed input and output memory layouts; x/0 = 0; reason: on rational inputs every value of a run is rational; x/0 = 0 is a value the machine can produce anyway; the layouts change no instance
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, STOC 2027 submission #829 (October 2026), §2, interface (i), p. 4 [Tar86]

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_SepQPTardos_Main_Machine
import Definitions.Def_SepQPTardos_Main_Layouts

open Matrix

namespace SepQPTardos.Main

/-- §2, interface (i) (Cui–Li–Miao, STOC 2027 #829, p. 4; [Tar86]): one admissible program of
the real RAM solves every linear program `min cᵀx` s.t. `D₁x = d₁`, `D₂x ≤ d₂`, `x_S ≥ 0`
(other variables free) with integer constraint matrices `D₁, D₂`. It returns an optimal
primal–dual pair, a Farkas certificate of infeasibility, or a feasible point and a ray of
negative cost. Its number of executed instructions is polynomial in `p₁ + p₂ + n + ⟨D₁⟩ + ⟨D₂⟩`
only (independent of `d₁, d₂, c`), and every number in every configuration of the run has
encoding length polynomial in the complete input. -/
theorem interface_i_tardos_lp :
    ∃ R : SmaleNinth.RAMProgram, Admissible R ∧ ∃ C k C' k' : ℕ,
      ∀ (p₁ p₂ n : ℕ) (D₁ : Matrix (Fin p₁) (Fin n) ℤ) (D₂ : Matrix (Fin p₂) (Fin n) ℤ)
        (S : Fin n → Bool) (d₁ : Fin p₁ → ℚ) (d₂ : Fin p₂ → ℚ) (c : Fin n → ℚ),
        ComputesWithin R (lpInput D₁ D₂ S d₁ d₂ c)
          (C * (p₁ + p₂ + n + intMatLen D₁ + intMatLen D₂ + 2) ^ k)
          (C' * (lpInputLen D₁ D₂ d₁ d₂ c + 2) ^ k')
          (LPOutputCorrect D₁ D₂ S d₁ d₂ c) := by sorry

end SepQPTardos.Main
