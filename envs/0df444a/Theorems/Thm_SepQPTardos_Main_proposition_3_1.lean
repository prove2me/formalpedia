-- Prove2me | Theorems.Thm_SepQPTardos_Main_proposition_3_1
-- name    : SepQPTardos.Main.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:15:00.979191+00:00
-- url     : https://prove2.me/theorems/8c660bb3-b202-44cc-9f3d-2f1345c32004
-- title:
--   Proposition 3.1 — local near-point solver in poly(r, m, ⟨A⟩, log B) operations
-- statement:
--   There is one admissible program of the real RAM and constants $C,k,C',k'$ with the following property. Let $A\in\mathbb Z^{r\times m}$, $q\in\mathbb Q^m_{\ge0}$, $c\in\mathbb Q^m$, an index set $F\subseteq[m]$, $a\in\mathbb Q^m$, $\varepsilon\in\mathbb Q_{>0}$ and an integer $B\ge1$, and put $b=Aa$. Suppose $a\in P_F(b)=\{x:Ax=b,\ x_{\bar F}\ge0\}$ and that the box $|x-a|\le B\varepsilon\mathbf 1$ contains an optimum of $\Phi$ on $P_F(b)$. Then on this input the program halts within
--
--   $$C\,(r+m+\langle A\rangle+\operatorname{size}(B)+2)^k$$
--
--   steps — independently of the encoding lengths of $a$, $\varepsilon$, $q$, $c$ — and returns $x\in P_F(b)$ with
--
--   $$\|x-z\|_\infty\le\varepsilon\tag{10}$$
--
--   for some optimum $z$ on $P_F(b)$. Every number held during the run is a rational of encoding length at most $C'(L+2)^{k'}$, $L$ the complete input length.
--
--   The revelation algorithm of §4 calls this solver at most $m$ times, with centre the trial point $t$, accuracy $\varepsilon=E_F/(4m\kappa)$ and $B=4m\kappa^2$.
--
--   Differences from the source:
--   - generalization: counts basic operations (addition, subtraction, multiplication, division, comparison) → counts every executed instruction of the real RAM, pointer and control instructions included; reason: a bound on all instructions implies the same bound on the arithmetic operations
--   - generalization: no bound on intermediate encoding lengths in the statement → every number of the run has encoding length polynomial in the complete input; reason: §4.5 (p. 11) argues this bound for the local solver and the proof of Theorem 1.1 needs it
--   - reading: a ∈ P_F(b) for the right-hand side b of the current problem → b = Aa, not a separate input; reason: a ∈ P_F(b) forces b = Aa
--   - encoding: poly(r, m, ⟨A⟩, log B) basic operations → C·(r + m + ⟨A⟩ + size B + 2)^k steps, constants fixed before the instance; reason: standard meaning of a polynomial bound; size B is the binary length of B
--   - encoding: binary encoding length, convention not fixed → ⟨z⟩ = 1 + size|z| for integers, ⟨p/q⟩ = ⟨p⟩ + size q in lowest terms, sums over entries; reason: all standard conventions agree up to polynomial factors
--   - encoding: rational arithmetic model, an algorithm → one admissible program (integer constants only) of the published real RAM SmaleNinth.RAMProgram with fixed input and output memory layouts; x/0 = 0; reason: on rational inputs every value of a run is rational; x/0 = 0 is a value the machine can produce anyway; the layouts change no instance
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, STOC 2027 submission #829 (October 2026), §3, Proposition 3.1 and the preceding paragraph, eq. (10), p. 6

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_SepQPTardos_Main_Problem
import Definitions.Def_SepQPTardos_Main_Machine
import Definitions.Def_SepQPTardos_Main_Analysis
import Definitions.Def_SepQPTardos_Main_Layouts

open Matrix

namespace SepQPTardos.Main

/-- Proposition 3.1 (local near-point solver; Cui–Li–Miao, STOC 2027 #829, p. 6): one
admissible program of the real RAM takes `A ∈ ℤ^{r×m}`, `q ≥ 0`, `c`, an index set `F`, a point
`a ∈ P_F(b) ∩ ℚ^m` (`b = Aa`), `ε ∈ ℚ_{>0}` and an integer `B ≥ 1` such that the box
`|x − a| ≤ Bε𝟙` contains an optimum on `P_F(b)`, and returns `x ∈ P_F(b)` with `‖x − z‖∞ ≤ ε`
for some optimum `z` on `P_F(b)` (eq. (10)). Its number of executed instructions is polynomial
in `r + m + ⟨A⟩ + log B`, independent of `a, ε, q, c`; every number of the run has encoding
length polynomial in the complete input. -/
theorem proposition_3_1 :
    ∃ R : SmaleNinth.RAMProgram, Admissible R ∧ ∃ C k C' k' : ℕ,
      ∀ (r m : ℕ) (A : Matrix (Fin r) (Fin m) ℤ) (q c : Fin m → ℚ) (F : Finset (Fin m))
        (a : Fin m → ℚ) (ε : ℚ) (B : ℕ),
        (∀ e, 0 ≤ q e) → 0 < ε → 1 ≤ B →
        castVec a ∈ PF A (castMat A *ᵥ castVec a) F →
        (∃ z, IsMinimizer (PF A (castMat A *ᵥ castVec a) F) (Phi (castVec q) (castVec c)) z ∧
          ∀ e, |z e - (a e : ℝ)| ≤ (B : ℝ) * (ε : ℝ)) →
        ComputesWithin R (localInput A q c F a ε B)
          (C * (r + m + intMatLen A + Nat.size B + 2) ^ k)
          (C' * (localInputLen A q c a ε B + 2) ^ k')
          (LocalOutputCorrect A q c F a ε) := by sorry

end SepQPTardos.Main
