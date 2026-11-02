-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P23_phase_polarization
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P23.phase_polarization
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:06:26.851841+00:00
-- url     : https://prove2.me/theorems/07851e36-4744-4914-b71c-e3d33dbc86fc
-- title:
--   Coherent polar encoding polarizes the phase channel
-- statement:
--   Let $U:\mathbb C^2\to\mathbb C^b\otimes\mathbb C^e$ be an isometry, so $U^\dagger U=I$, defining a memoryless channel to Bob and its fixed complementary channel to Eve. All binary inputs are uniform and entropies are in bits. At recursion depth $n\ge0$, let $N=2^n$ and apply the coherent Arikan encoder $G_N=B_NF^{\otimes n}$, where $F=\left(\begin{smallmatrix}1&0\\1&1\end{smallmatrix}\right)$. Amplitude synthesis retains previous bits and averages future bits; phase synthesis retains future bits and averages previous bits, with Bob's coherent copy register $C^N$ retained. Write $r(W)=\|\sqrt{\rho_0}\sqrt{\rho_1}\|_1=\sqrt{F(W)}$ for the root fidelity of a binary channel $W$. Fix $0<\beta<1/2$ and put $t_n=2^{-N^\beta}$. Let $G_A,G_P,G_E$ be the respective amplitude-good, phase-good, and Eve-amplitude-good sets, with the strict rule $r(W_N^{(i)})<t_n$. Write $\mathcal A=G_A\cap G_P$ and $\mathcal B=(G_A\cup G_P)^c$. Each set depends on $n$ and $\beta$.
--
--   The physical encoded purification for a phase string $x$ is
--   $$
--   |\sigma_{x,N}\rangle=2^{-N/2}\sum_{z\in\{0,1\}^N}(-1)^{x\cdot z}|\phi_{zG_N}\rangle^{B^NE^N}|z\rangle^{C^N}.
--   $$
--   Construct the synthesized phase channels from its $B^NC^N$ marginal with the reverse history convention above. If $I(W_P)$ is the single-use phase channel's symmetric Holevo information, then
--   $$
--   \lim_{n\to\infty}\frac{|G_P|}{2^n}=I(W_P).
--   $$
--   This identifies the asymptotic supply of phase-good positions for the coding scheme.
-- source:
--   Quantum polar codes for arbitrary channels, arXiv:1201.2906v2, PDF p. 3, I.B, Eq. (8)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P23

namespace QAlgorithms.Papers.Independent.Intakethird100.P23

open scoped BigOperators ComplexConjugate Matrix

open Filter

open QAlgorithms (Qubits)

open QAlgorithms.Papers.Independent.Information100.P67 (IsDegradable)

attribute [local instance] Classical.propDecidable

/-- Phase polarization for the actual Eq.(8) vector and reverse side information
(I.B, PDF pp.2–3); the limit is along N=2^n. -/
theorem phase_polarization {b e : ℕ} (U : Matrix (Fin b × Fin e) Bool ℂ)
    (hU : Uᴴ * U = 1) (beta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1 / 2) :
    Tendsto (fun n => indexRate (goodPhase U n beta)) atTop (nhds (phaseInformation U)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P23
