-- Prove2me | Theorems.Thm_ShorAlgorithms_QFT_path_amplitude
-- name    : ShorAlgorithms.QFT.path_amplitude
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T08:05:14.749255+00:00
-- url     : https://prove2.me/theorems/ef9a088c-c0ea-4ec1-b1c0-2b0f12363edf
-- title:
--   §4, eq. (4.5) — the amplitude of |a⟩ → |b⟩ through the QFT circuit
-- statement:
--   Let $l \ge 0$ and let $a = |a_{l-1} \dots a_0\rangle$ and $b = |b_{l-1} \dots b_0\rangle$ be $l$-bit basis states. Run the gate sequence
--   $$R_{l-1}\, S_{l-2,l-1}\, R_{l-2} \cdots R_1\, S_{0,l-1} \cdots S_{0,1}\, R_0$$
--   of Shor's eq. (4.4) on the basis state $|a\rangle$, where $R_j$ is the one-bit gate (4.2) on bit $j$ and $S_{j,k}$ is the two-bit phase gate (4.3) on bits $j < k$ with angle $\pi/2^{k-j}$. Then the amplitude of $|b\rangle$ in the resulting state is
--   $$\frac{1}{2^{l/2}}\exp\!\Big( i \Big( \sum_{0 \le j < l} \pi\, a_j b_j + \sum_{0 \le j < k < l} \frac{\pi}{2^{k-j}}\, a_j b_k \Big) \Big).$$
--
--   The factor $2^{-l/2} = q^{-1/2}$ collects the factors $1/\sqrt2$ of the $l$ gates $R_j$, and the phase is Shor's expression (4.5): $R_j$ contributes $\pi$ when $a_j = b_j = 1$, and $S_{j,k}$ contributes $\pi/2^{k-j}$ when the input bit $a_j$ and the output bit $b_k$ are both $1$. That the second sum pairs $a_j$ with $b_k$ records the order in which the gates act.
--
--   **Formalization Note** The circuit is run on the basis state $|a\rangle$ and the conclusion is the amplitude at $b$. The prefactor is written $(\sqrt{2^l})^{-1}$ and $k - j$ is natural-number subtraction under $j < k$.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1496, §4, eq. (4.5) ("To show that this operation actually performs a quantum Fourier transform, consider the amplitude of going from |a⟩ …")

import Mathlib
import Definitions.Def_ShorAlgorithms_QFT_BitStrings
import Definitions.Def_ShorAlgorithms_QFT_Circuit

namespace ShorAlgorithms.QFT

/-- Shor 1997, §4, eq. (4.5), p. 1496: the amplitude of going from `|a⟩` to `|b⟩` through the
gate sequence (4.4) is `2^{-l/2}` times `exp(i φ)`, where
`φ = ∑_{0 ≤ j < l} π a_j b_j + ∑_{0 ≤ j < k < l} (π / 2^{k-j}) a_j b_k`. -/
theorem path_amplitude (l : ℕ) (a b : Fin l → Fin 2) :
    runCircuit (qftGates l) (basisState a) b =
      ((Real.sqrt (2 ^ l) : ℝ) : ℂ)⁻¹ *
        Complex.exp
          (((∑ j : Fin l, Real.pi * ((a j : ℕ) : ℝ) * ((b j : ℕ) : ℝ)) +
              ∑ j : Fin l, ∑ k : Fin l,
                if j < k then
                  Real.pi / 2 ^ ((k : ℕ) - (j : ℕ)) * ((a j : ℕ) : ℝ) * ((b k : ℕ) : ℝ)
                else 0 : ℝ) * Complex.I) := by sorry

end ShorAlgorithms.QFT
