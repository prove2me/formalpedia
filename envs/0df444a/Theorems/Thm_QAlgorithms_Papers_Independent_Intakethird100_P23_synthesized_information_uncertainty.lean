-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P23_synthesized_information_uncertainty
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P23.synthesized_information_uncertainty
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:08:46.194321+00:00
-- url     : https://prove2.me/theorems/5459af25-34ef-4348-ae12-c9a0f7fb9bac
-- title:
--   Synthesized complementary information uncertainty
-- statement:
--   Let $U:\mathbb C^2\to\mathbb C^b\otimes\mathbb C^e$ be an isometry, so $U^\dagger U=I$, defining a memoryless channel to Bob and its fixed complementary channel to Eve. All binary inputs are uniform and entropies are in bits. At recursion depth $n\ge0$, let $N=2^n$ and apply the coherent Arikan encoder $G_N=B_NF^{\otimes n}$, where $F=\left(\begin{smallmatrix}1&0\\1&1\end{smallmatrix}\right)$. Amplitude synthesis retains previous bits and averages future bits; phase synthesis retains future bits and averages previous bits, with Bob's coherent copy register $C^N$ retained. Write $r(W)=\|\sqrt{\rho_0}\sqrt{\rho_1}\|_1=\sqrt{F(W)}$ for the root fidelity of a binary channel $W$.
--
--   For every recursion depth $n\ge0$ and position $i\in\{1,\ldots,N\}$, let $W_{P,N}^{(i)}$ be Bob's synthesized phase channel and $W_{E,N}^{(i)}$ Eve's synthesized amplitude channel, both constructed from this same $U$ and encoder. Then
--   $$
--   I(W_{P,N}^{(i)})+I(W_{E,N}^{(i)})\le1.
--   $$
--   Both informations are symmetric Holevo informations. This complementarity bounds simultaneous phase information at Bob and amplitude information at Eve.
-- source:
--   Quantum polar codes for arbitrary channels, arXiv:1201.2906v2, PDF p. 8, Appendix C, Eq. (11)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P23

namespace QAlgorithms.Papers.Independent.Intakethird100.P23

open scoped BigOperators ComplexConjugate Matrix

open Filter

open QAlgorithms (Qubits)

open QAlgorithms.Papers.Independent.Information100.P67 (IsDegradable)

attribute [local instance] Classical.propDecidable

/-- Synthesized complementary information uncertainty, Eq.(11), PDF p.8.
Neither degradability nor an uncertainty relation is a hypothesis. -/
theorem synthesized_information_uncertainty {b e : ℕ}
    (U : Matrix (Fin b × Fin e) Bool ℂ) (hU : Uᴴ * U = 1)
    (n : ℕ) (i : Fin (2 ^ n)) :
    symmetricInformation (phaseSplit U n i) +
      symmetricInformation (environmentSplit U n i) ≤ 1 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P23
