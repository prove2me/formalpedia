-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_ampEncoding_qram
-- name    : QAlgorithms.Nannicini.ampEncoding_qram
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:48:08.466533+00:00
-- url     : https://prove2.me/theorems/1e44ecf7-7509-43cd-9314-004a43afbe7d
-- title:
--   Amplitude encoding with O(log d) QRAM queries and O(log d (log d + log 1/ϵ)) two-qubit gates after Õ(d) classical preprocessing (corrected)
-- statement:
--   This is a corrected form of the QRAM speed-up for amplitude encoding.
--
--   **QRAM.** For words $M_j \in \{0,1\}^q$ indexed by $j \in \{0,1\}^a$, the QRAM is the unitary $U_{\mathrm{QRAM}} |j\rangle |y\rangle = |j\rangle |y \oplus M_j\rangle$ (Definition 5.39). Its size is $2^a q$.
--
--   **Classical preprocessing.** It is a straight-line program over the reals. It reads $\operatorname{Re} x_0, \operatorname{Im} x_0, \operatorname{Re} x_1, \dots$, and each instruction is one of $+, -, \times, \div, \sqrt{\cdot}, \arccos$, the complex argument, or a rational constant. Its cost is its number of instructions. Word $j$ of the QRAM is the $q$-bit binary expansion of the integer part of a designated program value.
--
--   **Circuit.** It acts on $n = \lceil \log_2 d \rceil$ output qubits plus $w$ ancillas, all starting in $|0\rangle$. It consists of arbitrary two-qubit gates and uncontrolled calls to $U_{\mathrm{QRAM}}$ (or its inverse).
--
--   There are constants $C > 0$ and $c \in \mathbb{N}$ such that for every $d \ge 1$ and every $\epsilon > 0$ there exist $a, q, w$, a program $P$, an address map and a circuit $Q$, none depending on $x$, with the following properties. Write $L = \log(2+d) + \log(2+1/\epsilon)$. Then:
--
--   1. the QRAM size satisfies $2^a q \le C d L^c$, and $P$ has at most $C d L^c$ instructions;
--   2. $Q$ makes at most $C \log(2+d)$ QRAM calls and uses at most $C \log(2+d)\, L$ two-qubit gates;
--   3. for every nonzero $x \in \mathbb{C}^d$, with the QRAM loaded by running $P$ on $x$,
--
--   $$
--   \bigl\| Q |0^{n+w}\rangle - |\mathrm{amp}(x)\rangle \otimes |0^w\rangle \bigr\| \le \epsilon .
--   $$
--
--   Once the classical data structure has been written, the state $|\mathrm{amp}(x)\rangle$ can be prepared with exponentially fewer gates than the $\tilde O(d)$ of Corollary 5.37.
--
--   **Formalization Note** The printed corollary claims $O(\log^2 d)$ gates for every $\epsilon$. Its proof, however, fixes the word size $q = O(\log d)$, which limits the reachable error. The statement therefore lets $q$, and with it the gate count, grow with $\log(1/\epsilon)$. For $\epsilon \ge 1/\mathrm{poly}(d)$ this is the printed bound. The source does not define its classical cost model; the one used here is fixed in the Lean definitions `ArithInstr` and `arithRun`.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 130, Corollary 5.45. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Nannicini_Ch05c_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini










/-- Corrected statement. Nannicini p.130, Corollary 5.45, as printed: "Given a classical
description of `x ∈ ℂ^d` in finite precision and a QRAM of size `Õ(d)`, there is a circuit that
implements the mapping `|0⟩ → |amp(x)⟩` with error at most `ϵ` using `O(log d)` QRAM queries,
`O(log² d)` additional gates, and `Õ(d)` classical arithmetic operations to initialize the QRAM
data structure."

What was changed. (1) The gate bound `O(log² d)` is replaced by
`O(log d · (log d + log(1/ϵ)))`, and the QRAM size and the classical cost `Õ(d)` may carry
polylogarithmic factors in `1/ϵ`. This is the source's own count on p.130, `O(n)` queries and
`O(nq)` gates with `n = log d` levels and word size `q`, with `q` allowed to grow like
`log d + log(1/ϵ)`; for `ϵ ≥ 1/poly(d)` it is the printed `O(log² d)`. (2) "Classical arithmetic
operations" are counted in the straight-line real-arithmetic model `ArithInstr` (one operation
per `+, −, ×, ÷, √, arccos, arg` or constant); the QRAM is written classically from the
program's values (`qramWords`).

Why. The printed proof fixes `q = O(log d)` independently of `ϵ` ("this already gives precision
exponential in d"), so its `O(log² d)` gates cannot reach an arbitrary error `ϵ`: fixed-point
words of `O(log d)` bits give error at least about `2^{-q}`. The source gives no cost model for
"classical arithmetic operations".

The model. The circuit runs on the `n = ⌈log d⌉` output qubits plus `w` ancillas that start in
`|0⟩`, over arbitrary two-qubit gates (Rem. 5.44: "additional (two-qubit) gates"), and calls the
QRAM `U_QRAM` of Def. 5.39 (address `a` qubits, words of `q` bits), uncontrolled, possibly as its
inverse. The circuit, the program and the addressing do not depend on `x`: `x` enters only through
the QRAM contents (Rem. 5.41). Error is the Euclidean distance from `|amp(x)⟩ ⊗ |0^w⟩`, as in
Cor. 5.37. The constants `C, c` come before `d`, `x`, `ϵ`. -/
theorem ampEncoding_qram :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ, ∀ d : ℕ, 1 ≤ d → ∀ ε : ℝ, 0 < ε →
      ∃ (a q w : ℕ) (P : List ArithInstr) (addr : Qubits a → ℕ)
        (circ : OracleCircuit twoQubitGateSet (fun _ : Fin 1 => a + q) (Nat.clog 2 d + w)),
        (2 : ℝ) ^ a * q ≤ C * d * (Real.log (2 + d) + Real.log (2 + 1 / ε)) ^ c ∧
        (P.length : ℝ) ≤ C * d * (Real.log (2 + d) + Real.log (2 + 1 / ε)) ^ c ∧
        (circ.queryCount 0 : ℝ) ≤ C * Real.log (2 + d) ∧
        (circ.gateCount : ℝ) ≤
          C * Real.log (2 + d) * (Real.log (2 + d) + Real.log (2 + 1 / ε)) ∧
        (∀ s ∈ circ, uncontrolledStep s) ∧
        ∀ x : Fin d → ℂ, x ≠ 0 →
          ‖act (circ.unitary fun _ => qramUnitary a q (qramWords a q P addr x))
              (zeroKet (Nat.clog 2 d + w)) -
            WithLp.toLp 2 (fun z : Qubits (Nat.clog 2 d + w) =>
              if ∀ k : Fin w, z (Fin.natAdd (Nat.clog 2 d) k) = false then
                padState (Nat.clog 2 d) (normalizedVec (WithLp.toLp 2 x))
                  (fun i => z (Fin.castAdd w i))
              else 0)‖ ≤ ε := by
  sorry



end QAlgorithms.Nannicini
