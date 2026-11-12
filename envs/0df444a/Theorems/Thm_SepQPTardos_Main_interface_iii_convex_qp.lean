-- Prove2me | Theorems.Thm_SepQPTardos_Main_interface_iii_convex_qp
-- name    : SepQPTardos.Main.interface_iii_convex_qp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:15:15.241966+00:00
-- url     : https://prove2.me/theorems/e3657174-74f0-4e56-b7e4-25c07c9e855e
-- title:
--   §2 interface (iii) — exact rational convex QP in time polynomial in the binary encoding [KTK80]
-- statement:
--   There is one admissible program of the real RAM and constants $C,k,C',k'$ such that for every rational convex quadratic program
--
--   $$\min\ \tfrac12x^\top Mx+c^\top x\quad\text{subject to}\quad Dx\le d,$$
--
--   with $M\in\mathbb Q^{n\times n}$ such that $M+M^\top$ is positive semidefinite (the objective is convex), $D\in\mathbb Q^{p\times n}$, $d\in\mathbb Q^p$, $c\in\mathbb Q^n$, the program halts within $C(L+2)^k$ steps, where $L$ is the complete binary encoding length of $(M,D,d,c)$ (with $n$ and $p$), and outputs correctly that the program is infeasible, that it is feasible and unbounded below, or an optimal point. Every number held during the run, in particular the optimal point, is a rational of encoding length at most $C'(L+2)^{k'}$.
--
--   The paper applies this to the compressed local QP of Proposition 3.1, whose encoding length is bounded by the structural input.
--
--   Differences from the source:
--   - generalization: counts basic operations (addition, subtraction, multiplication, division, comparison) → counts every executed instruction of the real RAM, pointer and control instructions included; reason: a bound on all instructions implies the same bound on the arithmetic operations
--   - reading: solved exactly in time polynomial in its complete binary encoding (a bit algorithm), simulated with polynomially many basic operations → real-RAM step count and encoding length of every intermediate number both at most polynomial in the complete binary encoding; reason: the block's last sentences state that the algorithm is used through this simulation; with polynomially long numbers the two forms are equivalent
--   - reading: solved exactly; in the feasible finite case a rational optimal point of polynomial encoding length → status 0 with an optimal point, status 1 if infeasible, status 2 if feasible and unbounded below; the length bound covers the output; reason: exact solution of a QP means deciding these three cases
--   - encoding: rational convex quadratic program → ½xᵀMx + cᵀx over Dx ≤ d with M + Mᵀ positive semidefinite; reason: these are exactly the rational convex quadratic programs; equalities are pairs of inequalities
--   - encoding: binary encoding length, convention not fixed → ⟨z⟩ = 1 + size|z| for integers, ⟨p/q⟩ = ⟨p⟩ + size q in lowest terms, sums over entries; reason: all standard conventions agree up to polynomial factors
--   - encoding: rational arithmetic model, an algorithm → one admissible program (integer constants only) of the published real RAM SmaleNinth.RAMProgram with fixed input and output memory layouts; x/0 = 0; reason: on rational inputs every value of a run is rational; x/0 = 0 is a value the machine can produce anyway; the layouts change no instance
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, STOC 2027 submission #829 (October 2026), §2, interface (iii), p. 4 [KTK80]

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_SepQPTardos_Main_Problem
import Definitions.Def_SepQPTardos_Main_Machine
import Definitions.Def_SepQPTardos_Main_Layouts

open Matrix

namespace SepQPTardos.Main

/-- §2, interface (iii) (Cui–Li–Miao, STOC 2027 #829, p. 4; [KTK80]): one admissible program of
the real RAM solves every rational convex quadratic program `min ½xᵀMx + cᵀx` s.t. `Dx ≤ d`
(convex: `M + Mᵀ` is positive semidefinite; `M` need not be symmetric). It reports
infeasibility, unboundedness below, or an optimal point. Its number of executed instructions
and the encoding length of every number of the run are polynomial in the complete binary
encoding of `(M, D, d, c)`. -/
theorem interface_iii_convex_qp :
    ∃ R : SmaleNinth.RAMProgram, Admissible R ∧ ∃ C k C' k' : ℕ,
      ∀ (n p : ℕ) (M : Matrix (Fin n) (Fin n) ℚ) (D : Matrix (Fin p) (Fin n) ℚ)
        (d : Fin p → ℚ) (c : Fin n → ℚ), (castQMat M + (castQMat M)ᵀ).PosSemidef →
        ComputesWithin R (cqpInput M D d c) (C * (cqpInputLen M D d c + 2) ^ k)
          (C' * (cqpInputLen M D d c + 2) ^ k') (CQPOutputCorrect M D d c) := by sorry

end SepQPTardos.Main
