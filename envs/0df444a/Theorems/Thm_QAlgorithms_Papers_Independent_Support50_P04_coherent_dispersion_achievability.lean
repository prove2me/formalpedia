-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P04_coherent_dispersion_achievability
-- name    : QAlgorithms.Papers.Independent.Support50.P04.coherent_dispersion_achievability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:40:49.757801+00:00
-- url     : https://prove2.me/theorems/8736d462-7d5f-4a20-ac6a-eb9c0b50c6c8
-- title:
--   Coherent-information dispersion achievability
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on finite positive-dimensional complex Hilbert spaces with fixed orthonormal bases. Write $\widehat R(n;\varepsilon)$ and $\widehat R^{\mathrm{cpp}}(n;\varepsilon)$ for the maximum unassisted and classical-post-processing assisted entanglement-transmission rates. A code has a positive integer message dimension $M$, rate $\log_2 M/n$, and squared fidelity to the normalized maximally entangled target at least $1-\varepsilon$. A cpp encoder may retain sender memory; its decoder is LOCC across that memory and the receiver outputs, with its final quantum output at the receiver and no preshared entanglement. Fix $0<\varepsilon<1$. All logarithms are binary and $\Phi^{-1}$ is the standard Gaussian quantile. Remainder constants may depend on the fixed channel and error, and are chosen before the block length: there are $C>0$ and $n_0\ge2$ such that the displayed bound holds for every integer $n\ge n_0$. For every normalized density input $\rho$, use the source purification with coefficients $(\sqrt\rho)_{ij}$ in the reference/input bases, and put $\omega^\rho=(\mathrm{id}\otimes\mathcal N)(\psi^\rho)$. Let $I_c(\mathcal N)=\max_\rho[S(B)_{\omega^\rho}-S(AB)_{\omega^\rho}]$, and let $\Pi_c$ be all maximizing density inputs, including rank-deficient ones. Let $V_c^\varepsilon$ be the minimum of $V(\omega^\rho\|I_A\otimes\omega_B^\rho)$ over $\Pi_c$ below $1/2$, and the maximum at or above $1/2$. Then
--
--   $$\widehat R(n;\varepsilon)\ge I_c(\mathcal N)+\sqrt{V_c^\varepsilon(\mathcal N)/n}\,\Phi^{-1}(\varepsilon)-C\log_2n/n.$$
--
--   This is a general achievable lower bound; it need not equal the optimal boundary.
-- source:
--   Quantum Coding with Finite Resources, arXiv:1504.04617v2, PDF p. 14, Theorem 6, Eqs. (48)–(50)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Support50.P04

variable {A B E : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- arXiv:1504.04617v2, PDF p.14, Theorem 6, Eqs.(48)–(50).
All normalized density inputs are allowed; min variance below 1/2 and max above.
This states only the source's one-sided achievable expansion. -/
theorem coherent_dispersion_achievability [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (epsilon : ℝ)
    (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    dispersionLower (fun n => unassistedBoundary N n epsilon)
      (channelCoherentBits N) (coherentInformationVariance N epsilon) epsilon := by sorry

end QAlgorithms.Papers.Independent.Support50.P04

end
