-- Prove2me | Theorems.Thm_SepQPTardos_Main_theorem_1_1
-- name    : SepQPTardos.Main.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:15:29.688191+00:00
-- url     : https://prove2.me/theorems/3866f57f-f0a2-4535-8747-063f17621ff1
-- title:
--   Theorem 1.1 — exact separable convex QP over integer equality constraints in poly(r, m, ⟨A⟩) operations
-- statement:
--   Consider problem (1),
--
--   $$\min\{\Phi(x): Ax=b,\ x\ge0\},\qquad \Phi(x)=\tfrac12\sum_{e=1}^mq_ex_e^2+\sum_{e=1}^mc_ex_e ,$$
--
--   with $A\in\mathbb Z^{r\times m}$, $b\in\mathbb Q^r$, $c\in\mathbb Q^m$ and $q\in\mathbb Q^m_{\ge0}$ (the quadratic weights may be zero). There is one admissible program $R$ of the real RAM — exact $+,-,\times,\div$ and comparisons at unit cost, integer program constants, no floor and no optimisation oracle — and constants $C,d,C',d'$ such that for **every** instance (every $r$ and $m$, with no full-rank, feasibility or boundedness assumption):
--
--   1. the run of $R$ on the instance halts within $C\,(r+m+\langle A\rangle+2)^d$ steps, a bound independent of the encoding lengths of $b$, $c$, $q$;
--   2. its output is correct: an optimal $x$ together with $\pi$ such that $(x,\pi)$ satisfies (8) (an exact optimal primal–dual pair), or a Farkas certificate $y$ with $A^\top y\ge0$, $b^\top y<0$, or a feasible $x$ and a direction $d$ with $Ad=0$, $d\ge0$, $d_e=0$ for $q_e>0$ and $c^\top d<0$, along which $\Phi(x+\lambda d)\to-\infty$;
--   3. every number in every register and memory cell at every step of this run is a rational of encoding length at most $C'(L+2)^{d'}$, where $L=r+m+\langle A\rangle+\langle b\rangle+\langle c\rangle+\langle q\rangle$.
--
--   For matrix classes with entries of polynomially bounded encoding, such as $\{0,\pm1\}$ matrices, this is a strongly polynomial algorithm.
--
--   Differences from the source:
--   - generalization: counts basic operations (addition, subtraction, multiplication, division, comparison) → counts every executed instruction of the real RAM, pointer and control instructions included; reason: a bound on all instructions implies the same bound on the arithmetic operations
--   - reading: a feasible point and a direction certifying unboundedness → a feasible x and d with Ad = 0, d ≥ 0, d_e = 0 for q_e > 0, cᵀd < 0; reason: for feasible x and d ≥ 0 with Ad = 0, Φ(x + λd) = Φ(x) + λ(Qx + c)ᵀd + (λ²/2)Σ q_e d_e² tends to −∞ iff d_N = 0 and cᵀd < 0; this is the certificate built on p. 5
--   - reading: an exact optimal primal–dual pair → x optimal by minimisation, and (x, π) satisfies (8); reason: both meanings are asserted; by (8) they are equivalent
--   - encoding: poly(r, m, ⟨A⟩) basic operations; encoding length polynomial in the complete input → C·(r + m + ⟨A⟩ + 2)^d steps and C'·(L + 2)^d' bits, with C, d, C', d' and the program fixed before the instance; reason: standard meaning of a polynomial bound uniform over all inputs
--   - encoding: binary encoding length, convention not fixed → ⟨z⟩ = 1 + size|z| for integers, ⟨p/q⟩ = ⟨p⟩ + size q in lowest terms, sums over entries; reason: all standard conventions agree up to polynomial factors
--   - encoding: rational arithmetic model, an algorithm → one admissible program (integer constants only) of the published real RAM SmaleNinth.RAMProgram with fixed input and output memory layouts; x/0 = 0; reason: on rational inputs every value of a run is rational; x/0 = 0 is a value the machine can produce anyway; the layouts change no instance
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, STOC 2027 submission #829 (October 2026), Theorem 1.1, p. 2

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_SepQPTardos_Main_Problem
import Definitions.Def_SepQPTardos_Main_Encoding
import Definitions.Def_SepQPTardos_Main_Machine
import Definitions.Def_SepQPTardos_Main_Layouts

namespace SepQPTardos.Main

/-- Theorem 1.1 (Cui–Li–Miao, STOC 2027 #829, p. 2). There is one admissible program `R` of the
real RAM (rational arithmetic `+ − × ÷` and comparisons at unit cost) and constants
`C, d, C', d'` such that for every instance of (1) — every `r, m`, every integer matrix
`A ∈ ℤ^{r×m}`, `b ∈ ℚ^r`, `c ∈ ℚ^m`, `q ∈ ℚ^m_{≥0}` — the run of `R` on the instance halts within
`C·(r + m + ⟨A⟩ + 2)^d` steps (independent of `b, c, q`) with a correct output: an optimal `x`
together with `π` satisfying (8), a Farkas certificate of infeasibility, or a feasible point
and a direction along which `Φ → −∞`; and every number held in a register or memory cell at
any step of that run is a rational of encoding length at most `C'·(L + 2)^{d'}`, `L` the
complete input length. -/
theorem theorem_1_1 :
    ∃ R : SmaleNinth.RAMProgram, Admissible R ∧ ∃ C d C' d' : ℕ,
      ∀ (r m : ℕ) (A : Matrix (Fin r) (Fin m) ℤ) (b : Fin r → ℚ) (c q : Fin m → ℚ),
        (∀ e, 0 ≤ q e) →
        ComputesWithin R (qpInput A b c q) (C * (r + m + intMatLen A + 2) ^ d)
          (C' * (qpInputLen A b c q + 2) ^ d') (QPOutputCorrect A b c q) := by sorry

end SepQPTardos.Main
