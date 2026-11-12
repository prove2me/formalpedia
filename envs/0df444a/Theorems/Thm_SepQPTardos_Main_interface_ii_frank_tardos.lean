-- Prove2me | Theorems.Thm_SepQPTardos_Main_interface_ii_frank_tardos
-- name    : SepQPTardos.Main.interface_ii_frank_tardos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:15:11.757552+00:00
-- url     : https://prove2.me/theorems/6063041b-304a-4137-804e-6b21445401a6
-- title:
--   §2 interface (ii), eq. (2) — Frank–Tardos compression in poly(d, log T) operations
-- statement:
--   There is one admissible program of the real RAM and constants $C,k,C',k'$ with the following property. Given $d\in\mathbb N$, $w\in\mathbb Q^d$ and an integer $T\ge2$, the program halts within $C\,(d+\operatorname{size}(T)+2)^k$ steps — a bound independent of $w$ — and returns $\bar w\in\mathbb Z^d$ with
--
--   $$\operatorname{sign}(w^\top a)=\operatorname{sign}(\bar w^\top a)\qquad\text{for all } a\in\mathbb Z^d,\ \|a\|_1\le T-1,\tag{2}$$
--
--   and $\|\bar w\|_\infty\le 2^{4d^3}T^{d(d+2)}$. Every number held during the run is a rational of encoding length at most $C'(d+\langle T\rangle+\langle w\rangle+2)^{k'}$.
--
--   In the local solver this compresses the objective coefficients so that the compressed QP has encoding length bounded by the structural input, while all comparisons and ties between integer points of the scaled box are preserved.
--
--   Differences from the source:
--   - generalization: counts basic operations (addition, subtraction, multiplication, division, comparison) → counts every executed instruction of the real RAM, pointer and control instructions included; reason: a bound on all instructions implies the same bound on the arithmetic operations
--   - encoding: sign(w⊤a) = sign(w̄⊤a) → SignType.sign of the real numbers wᵀa and w̄ᵀa, the sign 0 included; reason: (2) is an equality of signs; p. 7 uses it to preserve ties
--   - encoding: poly(d, log T) basic operations; intermediate encodings polynomial in the input → C·(d + size T + 2)^k steps and C'·(d + ⟨T⟩ + ⟨w⟩ + 2)^k' bits, constants fixed before the instance; reason: standard meaning of a polynomial bound uniform over all inputs
--   - encoding: binary encoding length, convention not fixed → ⟨z⟩ = 1 + size|z| for integers, ⟨p/q⟩ = ⟨p⟩ + size q in lowest terms, sums over entries; reason: all standard conventions agree up to polynomial factors
--   - encoding: rational arithmetic model, an algorithm → one admissible program (integer constants only) of the published real RAM SmaleNinth.RAMProgram with fixed input and output memory layouts; x/0 = 0; reason: on rational inputs every value of a run is rational; x/0 = 0 is a value the machine can produce anyway; the layouts change no instance
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, STOC 2027 submission #829 (October 2026), §2, interface (ii), eq. (2), p. 4 [FT87]

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_SepQPTardos_Main_Machine
import Definitions.Def_SepQPTardos_Main_Layouts

namespace SepQPTardos.Main

/-- §2, interface (ii), eq. (2) (Cui–Li–Miao, STOC 2027 #829, p. 4; [FT87]): one admissible
program of the real RAM takes `w ∈ ℚ^d` and an integer `T ≥ 2` and returns `w̄ ∈ ℤ^d` with
`sign(wᵀa) = sign(w̄ᵀa)` for all `a ∈ ℤ^d`, `‖a‖₁ ≤ T − 1`, and `‖w̄‖∞ ≤ 2^{4d³} T^{d(d+2)}`.
Its number of executed instructions is polynomial in `d + log T` (independent of `w`), and
every number of the run has encoding length polynomial in the input. -/
theorem interface_ii_frank_tardos :
    ∃ R : SmaleNinth.RAMProgram, Admissible R ∧ ∃ C k C' k' : ℕ,
      ∀ (d : ℕ) (w : Fin d → ℚ) (T : ℕ), 2 ≤ T →
        ComputesWithin R (ftInput w T) (C * (d + Nat.size T + 2) ^ k)
          (C' * (ftInputLen w T + 2) ^ k') (FTOutputCorrect w T) := by sorry

end SepQPTardos.Main
