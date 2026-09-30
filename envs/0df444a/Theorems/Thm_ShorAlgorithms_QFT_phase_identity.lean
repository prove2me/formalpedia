-- Prove2me | Theorems.Thm_ShorAlgorithms_QFT_phase_identity
-- name    : ShorAlgorithms.QFT.phase_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T08:08:21.840668+00:00
-- url     : https://prove2.me/theorems/f9fb1dee-a6a7-4e82-a4f0-29955991731f
-- title:
--   §4, eqs. (4.6)–(4.10) — the circuit phase equals 2πac/q modulo 2π
-- statement:
--   Let $l \ge 0$, $q = 2^l$, and let $a = (a_{l-1}, \dots, a_0)$ and $b = (b_{l-1}, \dots, b_0)$ be bit strings. Let $c$ be the bit reversal of $b$, $c_k = b_{l-1-k}$, and write
--   $$a = \sum_{j=0}^{l-1} 2^j a_j, \qquad c = \sum_{k=0}^{l-1} 2^k c_k$$
--   for the integers they encode (eq. (4.10)). Then the phase (4.5) agrees with $2\pi ac/q$ modulo $2\pi$:
--   $$\exp\!\Big( i \Big( \sum_{0 \le j < l} \pi\, a_j b_j + \sum_{0 \le j < k < l} \frac{\pi}{2^{k-j}}\, a_j b_k \Big) \Big) = \exp\!\Big( \frac{2\pi i\, a c}{q} \Big).$$
--
--   This is the arithmetic half of Shor's verification of the quantum Fourier transform circuit (eqs. (4.6)–(4.9)): it identifies the phase accumulated along the circuit with the phase of the $(a, c)$ entry of the Fourier matrix $A_q$. It is a statement about bits and involves no circuit.
--
--   **Formalization Note** "Agrees modulo $2\pi$" is stated as equality of the two unit complex numbers $e^{i\varphi}$. The values $a, c$ are natural numbers cast to $\mathbb C$.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), pp. 1496–1497, §4, eqs. (4.6)–(4.10) ("This expression can be rewritten as …")

import Mathlib
import Definitions.Def_ShorAlgorithms_QFT_BitStrings

namespace ShorAlgorithms.QFT

/-- Shor 1997, §4, eqs. (4.6)–(4.10), pp. 1496–1497: modulo `2π`, the phase (4.5) equals
`2π a c / q`, where `q = 2^l`, `a = ∑_j 2^j a_j` and `c = ∑_k 2^k c_k` is the bit reversal of
`b`. Stated as equality of the unit complex numbers `exp(i · phase)`. -/
theorem phase_identity (l : ℕ) (a b : Fin l → Fin 2) :
    Complex.exp
        (((∑ j : Fin l, Real.pi * ((a j : ℕ) : ℝ) * ((b j : ℕ) : ℝ)) +
            ∑ j : Fin l, ∑ k : Fin l,
              if j < k then
                Real.pi / 2 ^ ((k : ℕ) - (j : ℕ)) * ((a j : ℕ) : ℝ) * ((b k : ℕ) : ℝ)
              else 0 : ℝ) * Complex.I) =
      Complex.exp (2 * Real.pi * Complex.I * (bitsVal a : ℂ) * (bitsVal (bitRev b) : ℂ) /
        2 ^ l) := by sorry

end ShorAlgorithms.QFT
