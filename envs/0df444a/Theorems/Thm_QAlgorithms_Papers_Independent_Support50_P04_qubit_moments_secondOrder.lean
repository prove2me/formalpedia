-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P04_qubit_moments_secondOrder
-- name    : QAlgorithms.Papers.Independent.Support50.P04.qubit_moments_secondOrder
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:41:32.992882+00:00
-- url     : https://prove2.me/theorems/0d17838f-6838-4fc4-bb79-e2b9de7d06c7
-- title:
--   Dephasing moments and second-order boundary
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on finite positive-dimensional complex Hilbert spaces with fixed orthonormal bases. Write $\widehat R(n;\varepsilon)$ and $\widehat R^{\mathrm{cpp}}(n;\varepsilon)$ for the maximum unassisted and classical-post-processing assisted entanglement-transmission rates. A code has a positive integer message dimension $M$, rate $\log_2 M/n$, and squared fidelity to the normalized maximally entangled target at least $1-\varepsilon$. A cpp encoder may retain sender memory; its decoder is LOCC across that memory and the receiver outputs, with its final quantum output at the receiver and no preshared entanglement. Fix $0<\varepsilon<1$. All logarithms are binary and $\Phi^{-1}$ is the standard Gaussian quantile. Remainder constants may depend on the fixed channel and error, and are chosen before the block length: there are $C>0$ and $n_0\ge2$ such that the displayed bound holds for every integer $n\ge n_0$. Write $h(p)=-p\log_2p-(1-p)\log_2(1-p)$, with zero-weight terms zero, and $v(p)=p(\log_2p+h(p))^2+(1-p)(\log_2(1-p)+h(p))^2$. For every $0\le\gamma\le1$, put $\omega=(\mathrm{id}\otimes\mathcal Z_\gamma)(\Phi_2)$. Its coherent information and variance satisfy
--
--   $$I(A\rangle B)_\omega=1-h(\gamma),\qquad V(A\rangle B)_\omega=v(\gamma).$$
--
--   Moreover, with $t_n=1-h(\gamma)+\sqrt{v(\gamma)/n}\Phi^{-1}(\varepsilon)$,
--
--   $$t_n-C_-\log_2n/n\le\widehat R_{\mathcal Z_\gamma}(n;\varepsilon)\le t_n+C_+\log_2n/n$$
--
--   for all sufficiently large $n$. Each side has fixed positive constants and thresholds; they may be combined into a single remainder bound. This second-order result includes zero dispersion.
-- source:
--   Quantum Coding with Finite Resources, arXiv:1504.04617v2, PDF p. 15, Eqs. (58)–(60)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Support50.P04

variable {A B E : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- arXiv:1504.04617v2, PDF pp.4,15–16, Eqs.(58)–(60).
Printed h=1-gamma log gamma-(1-gamma)log(1-gamma) in (58); changed to Result 1's
binary entropy. The O(log n/n) statement includes zero-dispersion endpoints. -/
theorem qubit_moments_secondOrder (gamma epsilon : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1)
    (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    QAlgorithms.Papers.Independent.Dependency50.P36.stateCoherentInformationBits (choiState (QAlgorithms.Papers.Independent.Information100.P27.qubitDephasing (1-2*gamma))) = 1-QAlgorithms.Papers.Independent.Frontier18.P07.binaryEntropyBits gamma ∧
    QAlgorithms.Papers.Independent.Dependency50.P36.coherentVariance (choiState (QAlgorithms.Papers.Independent.Information100.P27.qubitDephasing (1-2*gamma))) = binaryVariance gamma ∧
    dispersionLower (fun n => unassistedBoundary (QAlgorithms.Papers.Independent.Information100.P27.qubitDephasing (1-2*gamma)) n epsilon)
      (1-QAlgorithms.Papers.Independent.Frontier18.P07.binaryEntropyBits gamma) (binaryVariance gamma) epsilon ∧
    dispersionUpper (fun n => unassistedBoundary (QAlgorithms.Papers.Independent.Information100.P27.qubitDephasing (1-2*gamma)) n epsilon)
      (1-QAlgorithms.Papers.Independent.Frontier18.P07.binaryEntropyBits gamma) (binaryVariance gamma) epsilon := by sorry

end QAlgorithms.Papers.Independent.Support50.P04

end
