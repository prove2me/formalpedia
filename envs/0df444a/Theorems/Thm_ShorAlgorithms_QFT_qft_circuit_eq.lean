-- Prove2me | Theorems.Thm_ShorAlgorithms_QFT_qft_circuit_eq
-- name    : ShorAlgorithms.QFT.qft_circuit_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T08:15:54.679575+00:00
-- url     : https://prove2.me/theorems/9d8b48d1-89d5-4a28-ad44-8fcb5209adcf
-- title:
--   The QFT circuit (4.4) maps |a⟩ to q^{-1/2} ∑_b exp(2πiac/q)|b⟩, c = bit reversal of b
-- statement:
--   Let $l \ge 0$ and $q = 2^l$. Run Shor's gate sequence (4.4),
--   $$R_{l-1}\, S_{l-2,l-1}\, R_{l-2}\, S_{l-3,l-1}\, S_{l-3,l-2}\, R_{l-3} \cdots R_1\, S_{0,l-1} \cdots S_{0,2}\, S_{0,1}\, R_0$$
--   (applied from left to right; $R_j$ the one-bit gate (4.2) on bit $j$, $S_{j,k}$ the two-bit phase gate (4.3) with angle $\pi/2^{k-j}$), on the basis state $|a\rangle = |a_{l-1} \dots a_0\rangle$, where $a = \sum_j 2^j a_j$. The result is the state
--   $$\frac{1}{q^{1/2}} \sum_{b} \exp(2\pi i\, a c / q)\, |b\rangle,$$
--   the sum over all $l$-bit strings $b$, where $c = \sum_k 2^k c_k$ with $c_k = b_{l-1-k}$ is the bit reversal of $b$.
--
--   Since the $(a, c)$ entry of Shor's Fourier matrix $A_q$ (eq. (4.1)) is $q^{-1/2}\exp(2\pi i ac/q)$, the circuit computes $A_q$ followed by a reversal of the order of the output bits. The circuit consists of $l$ one-bit gates and $l(l-1)/2$ two-bit gates, which is what makes the Fourier sampling steps of Shor's factoring and discrete logarithm algorithms efficient.
--
--   **Formalization Note** The statement is made on basis states $|a\rangle$, as in the paper; by linearity of the circuit it determines the action on every state. The conclusion is an equality of functions: the output amplitude at every bit string $b$ is $(\sqrt{2^l})^{-1}\exp(2\pi i\, a c/2^l)$. The case $l = 0$ ($q = 1$, empty circuit) is included.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1496, §4 ("Applying this sequence of transformations will result in a quantum state …"); A_q from p. 1495, eq. (4.1)

import Mathlib
import Definitions.Def_ShorAlgorithms_QFT_BitStrings
import Definitions.Def_ShorAlgorithms_QFT_Circuit

namespace ShorAlgorithms.QFT

/-- Shor 1997, §4, p. 1496: with `q = 2^l`, the gate sequence (4.4) takes the basis state `|a⟩`
to `q^{-1/2} ∑_b exp(2π i a c / q) |b⟩`, where `c` is the bit reversal of `b`. That is, the
circuit computes the Fourier transform `A_q` of eq. (4.1) followed by a reversal of the output
bits. -/
theorem qft_circuit_eq (l : ℕ) (a : Fin l → Fin 2) :
    runCircuit (qftGates l) (basisState a) =
      fun b => ((Real.sqrt (2 ^ l) : ℝ) : ℂ)⁻¹ *
        Complex.exp (2 * Real.pi * Complex.I * (bitsVal a : ℂ) * (bitsVal (bitRev b) : ℂ) /
          2 ^ l) := by sorry

end ShorAlgorithms.QFT
