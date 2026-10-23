-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P33_depolarizing_spectrum_entropies
-- name    : QAlgorithms.Papers.Independent.Gap48.P33.depolarizing_spectrum_entropies
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:39:55.836038+00:00
-- url     : https://prove2.me/theorems/6f35141f-8ccf-416a-aacb-8fd057acc98b
-- title:
--   full depolarizing output spectrum, entropies, and loss
-- statement:
--   For $p,q\in[0,1]$, send the signal part of $|\Psi_-(q)\rangle=\sqrt{1-q}|10\rangle-\sqrt q|01\rangle$ through the total-Pauli-error channel $\mathcal N_p$. The printed order here is signal then reference. With $P_\eta=|\eta\rangle\langle\eta|$ and the constructed q-basis of (5.5),
--
--   $$\rho_{Q'R}=(1-p)P_{\Psi_-(q)}+\frac p3\left(P_{\Phi_-(q)}+P_{\Phi_+(1-q)}+P_{\Psi_+(1-q)}\right).$$
--
--   The remaining q-basis vectors are $|\Phi_-(q)\rangle=\sqrt{1-q}|00\rangle-\sqrt q|11\rangle$, $|\Phi_+(q)\rangle=\sqrt q|00\rangle+\sqrt{1-q}|11\rangle$, and $|\Psi_+(q)\rangle=\sqrt q|10\rangle+\sqrt{1-q}|01\rangle$. Its eigenvalue multiset is
--
--   $$\lambda=\left\{\frac{2p(1-q)}3,\frac{2pq}3,\frac{1-2p/3+\Delta}2,\frac{1-2p/3-\Delta}2\right\},\quad\Delta=\sqrt{(1-2p/3)^2-\frac{16}3p(1-p)q(1-q)}.$$
--
--   Writing $H(\lambda)=-\sum_j\lambda_j\log_2\lambda_j$, one has $S_e=S(Q'R)=H(\lambda)$, $S_{\rm in}=H_2(q)$, $S_{\rm out}=H_2(q+\frac{2p}3(1-2q))$, $L_Q=S_{\rm in}-S_{\rm out}+S_e$, and $I_Q=2H_2(q)-L_Q$. This computes the full output rather than postulating its spectral data.
--
--   Here $H_2$ denotes binary Shannon entropy in bits, with $0\log 0=0$.
-- source:
--   On the von Neumann capacity of noisy quantum channels, arXiv:quant-ph/9609024v3, PDF p. 11, V.A, (5.12)–(5.17): full depolarizing output spectrum, entropies, and loss

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P33

namespace QAlgorithms.Papers.Independent.Gap48.P33

open scoped BigOperators Matrix ComplexConjugate

-- Reuse only definitions from the pinned accepted library; no imported theorem is used.

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average labelInformation)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation first both)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange inputMutualInfo)

open QAlgorithms.Papers.Independent.Claimed50.P03 (pauliWeight wordSupport)

/-- PDF p.11, (5.12)–(5.17): actual output, eigenvalue multiset, entropies and loss.
The characteristic polynomial gives the multiset without arbitrary eigenvalue ordering. -/
theorem depolarizing_spectrum_entropies (p q : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    depolarizingOutput p q = ((1 - p : ℝ) : ℂ) • pureDensity (qBasis 0 q) +
      ((p / 3 : ℝ) : ℂ) • (pureDensity (qBasis 1 q) +
        pureDensity (qBasis 2 (1 - q)) + pureDensity (qBasis 3 (1 - q))) ∧
    IsDensityMatrix (depolarizingOutput p q) ∧
    (depolarizingOutput p q).charpoly =
      (∏ j : Fin 4, (Polynomial.X - Polynomial.C (depolarizingSpectrum p q j : ℂ))) ∧
    vnEntropy (depolarizingOutput p q) = shannon (depolarizingSpectrum p q) ∧
    entropyExchange (pauliDepolarizing p) (diagonalSource q) = shannon (depolarizingSpectrum p q) ∧
    vnEntropy (traceLeft (depolarizingOutput p q)) =
      binEntropy2 (q + (2 * p / 3) * (1 - 2 * q)) ∧
    vnEntropy (diagonalSource q) = binEntropy2 q ∧
    loss (pauliDepolarizing p) (diagonalSource q) = binEntropy2 q -
      binEntropy2 (q + (2 * p / 3) * (1 - 2 * q)) + shannon (depolarizingSpectrum p q) ∧
    mutualInformation (depolarizingOutput p q) =
      2 * binEntropy2 q - loss (pauliDepolarizing p) (diagonalSource q) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P33
