-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P23_synthesized_fidelity_uncertainty
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P23.synthesized_fidelity_uncertainty
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:09:25.391629+00:00
-- url     : https://prove2.me/theorems/e6612bfe-2770-43ff-8c12-a277c133d7fa
-- title:
--   Two synthesized fidelity uncertainty inequalities
-- statement:
--   Let $U:\mathbb C^2\to\mathbb C^b\otimes\mathbb C^e$ be an isometry, so $U^\dagger U=I$, defining a memoryless channel to Bob and its fixed complementary channel to Eve. All binary inputs are uniform and entropies are in bits. At recursion depth $n\ge0$, let $N=2^n$ and apply the coherent Arikan encoder $G_N=B_NF^{\otimes n}$, where $F=\left(\begin{smallmatrix}1&0\\1&1\end{smallmatrix}\right)$. Amplitude synthesis retains previous bits and averages future bits; phase synthesis retains future bits and averages previous bits, with Bob's coherent copy register $C^N$ retained. Write $r(W)=\|\sqrt{\rho_0}\sqrt{\rho_1}\|_1=\sqrt{F(W)}$ for the root fidelity of a binary channel $W$.
--
--   For every recursion depth $n\ge0$ and position $i\in\{1,\ldots,N\}$, the synthesized channels from this common physical construction obey both inequalities
--   $$
--   2r(W_{P,N}^{(i)})+r(W_{E,N}^{(i)})\ge1,
--   \qquad
--   r(W_{P,N}^{(i)})+2r(W_{E,N}^{(i)})\ge1.
--   $$
--   Root fidelities may equal zero or one. These estimates quantify the inability of the two complementary synthesized channels to be simultaneously reliable.
-- source:
--   Quantum polar codes for arbitrary channels, arXiv:1201.2906v2, PDF p. 8, Appendix C, Eq. (13)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P23

namespace QAlgorithms.Papers.Independent.Intakethird100.P23

open scoped BigOperators ComplexConjugate Matrix

open Filter

open QAlgorithms (Qubits)

open QAlgorithms.Papers.Independent.Information100.P67 (IsDegradable)

attribute [local instance] Classical.propDecidable

/-- Both fidelity uncertainty inequalities, Eq.(13), PDF pp.8–9.
Here channelRootFidelity is the square root of the paper's squared F. -/
theorem synthesized_fidelity_uncertainty {b e : ℕ}
    (U : Matrix (Fin b × Fin e) Bool ℂ) (hU : Uᴴ * U = 1)
    (n : ℕ) (i : Fin (2 ^ n)) :
    1 ≤ 2 * channelRootFidelity (phaseSplit U n i) +
      channelRootFidelity (environmentSplit U n i) ∧
    1 ≤ channelRootFidelity (phaseSplit U n i) +
      2 * channelRootFidelity (environmentSplit U n i) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P23
