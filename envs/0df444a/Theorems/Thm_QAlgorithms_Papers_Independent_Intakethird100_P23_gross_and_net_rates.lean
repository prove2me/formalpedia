-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P23_gross_and_net_rates
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P23.gross_and_net_rates
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:07:17.605146+00:00
-- url     : https://prove2.me/theorems/9c2d7446-4b6b-44c9-bed7-83e17ea60d75
-- title:
--   Gross and signed net polar index rates
-- statement:
--   Let $U:\mathbb C^2\to\mathbb C^b\otimes\mathbb C^e$ be an isometry, so $U^\dagger U=I$, defining a memoryless channel to Bob and its fixed complementary channel to Eve. All binary inputs are uniform and entropies are in bits. At recursion depth $n\ge0$, let $N=2^n$ and apply the coherent Arikan encoder $G_N=B_NF^{\otimes n}$, where $F=\left(\begin{smallmatrix}1&0\\1&1\end{smallmatrix}\right)$. Amplitude synthesis retains previous bits and averages future bits; phase synthesis retains future bits and averages previous bits, with Bob's coherent copy register $C^N$ retained. Write $r(W)=\|\sqrt{\rho_0}\sqrt{\rho_1}\|_1=\sqrt{F(W)}$ for the root fidelity of a binary channel $W$. Fix $0<\beta<1/2$ and put $t_n=2^{-N^\beta}$. Let $G_A,G_P,G_E$ be the respective amplitude-good, phase-good, and Eve-amplitude-good sets, with the strict rule $r(W_N^{(i)})<t_n$. Write $\mathcal A=G_A\cap G_P$ and $\mathcal B=(G_A\cup G_P)^c$. Each set depends on $n$ and $\beta$.
--
--   For every $n$, the exact identity is
--   $$
--   |\mathcal A|-|\mathcal B|=|G_A|+|G_P|-N.
--   $$
--   There exist real limits $a=\lim_n |\mathcal A|/N$ and $b_c=\lim_n |\mathcal B|/N$, and they satisfy
--   $$
--   a=I(W_A)+I(W_P)-1+b_c=I_c(U)+b_c,
--   \qquad
--   \lim_{n\to\infty}\frac{|\mathcal A|-|\mathcal B|}{N}=I_c(U).
--   $$
--   Here $I(W_A)$ and $I(W_P)$ are symmetric Holevo informations, and $I_c(U)=H(B)-H(E)=H(B)-H(AB)$ is evaluated on the purification of the maximally mixed qubit input. The net rate is a signed real quantity.
--
--   These identities distinguish generated and consumed ebits without optimizing or regularizing coherent information.
-- source:
--   Quantum polar codes for arbitrary channels, arXiv:1201.2906v2, PDF p. 6, Appendix A, Eq. (10)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P23

namespace QAlgorithms.Papers.Independent.Intakethird100.P23

open scoped BigOperators ComplexConjugate Matrix

open Filter

open QAlgorithms (Qubits)

open QAlgorithms.Papers.Independent.Information100.P67 (IsDegradable)

attribute [local instance] Classical.propDecidable

/-- Exact set identity, existence of gross-rate limits, Eq.(10), and signed
net-rate limit (Appendix A, PDF p.6). Casts precede subtraction. -/
theorem gross_and_net_rates {b e : ℕ} (U : Matrix (Fin b × Fin e) Bool ℂ)
    (hU : Uᴴ * U = 1) (beta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1 / 2) :
    (∀ n, ((informationSet U n beta).card : ℝ) - ((consumedSet U n beta).card : ℝ) =
      ((goodAmplitude U n beta).card : ℝ) + ((goodPhase U n beta).card : ℝ) -
        ((2 ^ n : ℕ) : ℝ)) ∧
    (∃ generated consumed : ℝ,
      Tendsto (fun n => indexRate (informationSet U n beta)) atTop (nhds generated) ∧
      Tendsto (fun n => indexRate (consumedSet U n beta)) atTop (nhds consumed) ∧
      generated = amplitudeInformation U + phaseInformation U - 1 + consumed ∧
      generated = symmetricCoherentInformation U + consumed) ∧
    Tendsto (fun n => indexRate (informationSet U n beta) - indexRate (consumedSet U n beta))
      atTop (nhds (symmetricCoherentInformation U)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P23
