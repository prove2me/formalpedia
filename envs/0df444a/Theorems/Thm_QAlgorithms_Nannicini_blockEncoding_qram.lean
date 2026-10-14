-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_blockEncoding_qram
-- name    : QAlgorithms.Nannicini.blockEncoding_qram
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:53:31.649264+00:00
-- url     : https://prove2.me/theorems/e5c48013-6243-4a88-b88e-d3ee54ec39ad
-- title:
--   A (‖A‖_F, Õ(q), ξ)-block-encoding of a classical matrix from QRAM, with an explicit cost model
-- statement:
--   Fix constants $C_0 \in \mathbb{R}$ and $c_0 \in \mathbb{N}$ (those of the assumption $p = \widetilde{O}(1)$). There are constants $C > 0$ and $c \in \mathbb{N}$ such that the following holds. Let $q, p \in \mathbb{N}$, $d = 2^q$, $\xi > 0$, write $L = \log(2+d) + \log(2+1/\xi)$, and assume $p \le C_0 L^{c_0}$. Then there exist
--
--   1. a QRAM (Def. 5.39) with $2^b$ addresses and words of $r$ bits, of size $2^b r \le C d^2 (p+1) L^c$;
--   2. a straight-line real-arithmetic program of at most $C d^2 L^c$ operations ($+, -, \times, \div, \sqrt{\cdot}, \arccos$, complex argument, rational constants) and an addressing map, which compute the QRAM contents from the entries of the matrix;
--   3. a quantum circuit $\mathcal{V}$ on $w + q$ qubits with $w \le C (q+1) L^c$, making at most $C L^c$ uncontrolled calls to the QRAM (or its inverse) and using at most $C L^c$ two-qubit gates,
--
--   all independent of the matrix, such that for every $A \in \mathbb{C}^{d\times d}$ whose entries satisfy $|\operatorname{Re} a_{ij}|, |\operatorname{Im} a_{ij}| \le 2^p$, the unitary $\mathcal{V}(U_{\mathrm{QRAM}}(A))$ obtained with the QRAM loaded by the program is an $(\|A\|_F, w, \xi)$-block-encoding of $A$:
--
--   $$
--   \bigl\| \|A\|_F\,(\langle 0|_w \otimes I)\,\mathcal{V}\,(|0\rangle_w \otimes I) - A \bigr\| \le \xi .
--   $$
--
--   This is the data-structure route to block-encodings of classically stored dense matrices, with subnormalization the Frobenius norm and only polylogarithmic quantum cost.
--
--   **Formalization Note** Corrected statement. The source gives no cost model for classical arithmetic, does not say in which parameters $p$ is polylogarithmic, and does not say how the costs depend on $\xi$. Here classical cost is the length of a straight-line real-arithmetic program (the model of the Cor. 5.45 chunk), $p = \widetilde{O}(1)$ means $p \le C_0 L^{c_0}$ for arbitrary $C_0, c_0$, all $\widetilde{O}$ bounds are polylogarithmic in $d$ and $1/\xi$, and the QRAM size is $\widetilde{O}(d^2 p)$ rather than $O(d^2 p)$ because the word size must grow with $\log(1/\xi)$. A $p$-bit entry is modelled by the magnitude bound $2^p$ on its real and imaginary parts.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 168, Proposition 7.29. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_QAlgorithms_Nannicini_Ch07b_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini












/-- Corrected statement. Nannicini p.168, Proposition 7.29 (adapted from [Chakraborty et al.,
2019, Kerenidis and Prakash, 2017]), as printed: "Let `d = 2^q` and `A ∈ ℂ^{d×d}`. Suppose we
have a classical finite-precision description of the entries of `A` with `p` bits each, and
assume `p = Õ(1)`. Then, given a QRAM of size `O(d²p)`, we can implement a
`(‖A‖_F, Õ(q), ξ)`-block-encoding of `A` using `Õ(1)` accesses to the QRAM and additional gates,
and `Õ(d²)` classical arithmetic operations to initialize the QRAM data structures."

What was changed. (1) Cost model: "classical arithmetic operations" are counted in the
straight-line real-arithmetic model `ArithOp` (one operation per `+, −, ×, ÷, √, arccos, arg`
or constant); the QRAM of Def. 5.39 (`qramOp`) is written classically from the program's values
(`qramMatrixWords`); the circuit, the program and the addressing are fixed before `A`, which
enters only through the QRAM contents. (2) "`p = Õ(1)`" is the hypothesis
`p ≤ C₀ (log(2+d) + log(2+1/ξ))^{c₀}`, with `C₀, c₀` quantified universally before the theorem's
constants: polylogarithmic in `d` and `1/ξ`, the reading of p.168 ("the required precision is
only polylogarithmically large"). (3) "`p` bits each" is the magnitude bound
`|Re a_ij|, |Im a_ij| ≤ 2^p`, which every `p`-bit fixed-point description satisfies wherever its
binary point sits; the statement is for every such `A`. (4) The dependence on `ξ` is explicit:
the `Õ(·)` bounds are `C · (·) · L^c` with `L = log(2+d) + log(2+1/ξ)` (Def. 1.11; p.169: "the
dependence on `ϵ` is polylogarithmic"), and the QRAM size is `Õ(d² p)` = `C d² (p+1) L^c`
rather than `O(d²p)`: the word size of the data structure must grow like `log(1/ξ)` to reach
error `ξ` (the same correction as for Cor. 5.45, on which the proof rests). `Õ(q)` auxiliary
qubits is `C (q+1) L^c`.

Why. The printed claim has no cost model for classical arithmetic, does not say in which
parameters `p` is polylogarithmic, and claims `Õ(1)` gates for an unspecified `ξ` without saying
how they depend on `ξ`; the `O(d²p)` QRAM size with fixed word size `p` cannot reach an
arbitrary `ξ`.

Model. The circuit acts on `w` auxiliary qubits followed by the `q` system qubits, over two-qubit
gates ("additional gates", Rem. 5.44), and calls the QRAM (address `b` qubits, words of `r`
bits) uncontrolled, possibly as its inverse. The block-encoding is the frozen `IsBlockEncoding`
(Def. 7.11, auxiliary register first) with `α = ‖A‖_F` (`frobNorm`, Def. 7.28) and error `ξ`; `A`
is read on qubits through the most-significant-bit-first index map `bitsEquivFin`. -/
theorem blockEncoding_qram :
    ∀ (C₀ : ℝ) (c₀ : ℕ), ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ, ∀ (q p : ℕ) (ξ : ℝ), 0 < ξ →
      (p : ℝ) ≤ C₀ * (Real.log (2 + (2 : ℝ) ^ q) + Real.log (2 + 1 / ξ)) ^ c₀ →
      ∃ (w b r : ℕ) (Prog : List ArithOp) (addr : Qubits b → ℕ)
        (circ : OracleCircuit twoQubitGateSet (fun _ : Fin 1 => b + r) (w + q)),
        (2 : ℝ) ^ b * r ≤ C * ((2 : ℝ) ^ q) ^ 2 * ((p : ℝ) + 1) *
          (Real.log (2 + (2 : ℝ) ^ q) + Real.log (2 + 1 / ξ)) ^ c ∧
        (Prog.length : ℝ) ≤ C * ((2 : ℝ) ^ q) ^ 2 *
          (Real.log (2 + (2 : ℝ) ^ q) + Real.log (2 + 1 / ξ)) ^ c ∧
        (circ.queryCount 0 : ℝ) ≤ C * (Real.log (2 + (2 : ℝ) ^ q) + Real.log (2 + 1 / ξ)) ^ c ∧
        (circ.gateCount : ℝ) ≤ C * (Real.log (2 + (2 : ℝ) ^ q) + Real.log (2 + 1 / ξ)) ^ c ∧
        (w : ℝ) ≤ C * ((q : ℝ) + 1) * (Real.log (2 + (2 : ℝ) ^ q) + Real.log (2 + 1 / ξ)) ^ c ∧
        (∀ s ∈ circ, match s with
          | OracleStep.query _ _ ctrl _ _ => ctrl = none
          | OracleStep.gate _ => True) ∧
        ∀ A : Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℂ,
          (∀ i j, |(A i j).re| ≤ (2 : ℝ) ^ p ∧ |(A i j).im| ≤ (2 : ℝ) ^ p) →
          IsBlockEncoding (0 : Qubits w)
            ((circ.unitary fun _ => qramOp b r (qramMatrixWords b r Prog addr A)).submatrix
              (qubitsAppendEquiv w q).symm (qubitsAppendEquiv w q).symm)
            (frobNorm (A.submatrix (bitsEquivFin q) (bitsEquivFin q))) ξ
            (A.submatrix (bitsEquivFin q) (bitsEquivFin q)) := by
  sorry

end QAlgorithms.Nannicini
