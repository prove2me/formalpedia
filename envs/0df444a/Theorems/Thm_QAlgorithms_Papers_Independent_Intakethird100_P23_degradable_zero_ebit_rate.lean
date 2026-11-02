-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P23_degradable_zero_ebit_rate
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P23.degradable_zero_ebit_rate
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:08:01.743812+00:00
-- url     : https://prove2.me/theorems/54afd944-8d8f-47dd-9ad7-917289dac641
-- title:
--   Degradability makes the entanglement consumption rate vanish
-- statement:
--   Let $U:\mathbb C^2\to\mathbb C^b\otimes\mathbb C^e$ be an isometry, so $U^\dagger U=I$, defining a memoryless channel to Bob and its fixed complementary channel to Eve. All binary inputs are uniform and entropies are in bits. At recursion depth $n\ge0$, let $N=2^n$ and apply the coherent Arikan encoder $G_N=B_NF^{\otimes n}$, where $F=\left(\begin{smallmatrix}1&0\\1&1\end{smallmatrix}\right)$. Amplitude synthesis retains previous bits and averages future bits; phase synthesis retains future bits and averages previous bits, with Bob's coherent copy register $C^N$ retained. Write $r(W)=\|\sqrt{\rho_0}\sqrt{\rho_1}\|_1=\sqrt{F(W)}$ for the root fidelity of a binary channel $W$. Fix $0<\beta<1/2$ and put $t_n=2^{-N^\beta}$. Let $G_A,G_P,G_E$ be the respective amplitude-good, phase-good, and Eve-amplitude-good sets, with the strict rule $r(W_N^{(i)})<t_n$. Write $\mathcal A=G_A\cap G_P$ and $\mathcal B=(G_A\cup G_P)^c$. Each set depends on $n$ and $\beta$.
--
--   Assume that there is a completely positive trace-preserving map $D:B\to E$ with $\mathcal N^c=D\circ\mathcal N$ for the fixed extension $U$. Then
--   $$
--   \lim_{n\to\infty}\frac{|\mathcal B|}{2^n}=0.
--   $$
--   This concerns asymptotic consumption per channel use; the finite-blocklength set $\mathcal B$ need not be empty.
-- source:
--   Quantum polar codes for arbitrary channels, arXiv:1201.2906v2, PDF p. 9, II and Appendix C

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P23

namespace QAlgorithms.Papers.Independent.Intakethird100.P23

open scoped BigOperators ComplexConjugate Matrix

open Filter

open QAlgorithms (Qubits)

open QAlgorithms.Papers.Independent.Information100.P67 (IsDegradable)

attribute [local instance] Classical.propDecidable

/-- The consumed-ebit RATE vanishes for degradable channels; this is not a
finite-blocklength zero-consumption assertion (II, Appendix C, PDF pp.4,8–9). -/
theorem degradable_zero_ebit_rate {b e : ℕ} (U : Matrix (Fin b × Fin e) Bool ℂ)
    (hU : Uᴴ * U = 1) (hdeg : IsDegradable U)
    (beta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1 / 2) :
    Tendsto (fun n => indexRate (consumedSet U n beta)) atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P23
