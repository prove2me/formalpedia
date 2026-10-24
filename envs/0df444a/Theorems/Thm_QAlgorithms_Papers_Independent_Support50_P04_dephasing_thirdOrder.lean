-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P04_dephasing_thirdOrder
-- name    : QAlgorithms.Papers.Independent.Support50.P04.dephasing_thirdOrder
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:27:01.747618+00:00
-- url     : https://prove2.me/theorems/ee1c8619-6e37-48dd-989e-2942fa4eb90e
-- title:
--   Qubit dephasing: third-order boundary
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on finite positive-dimensional complex Hilbert spaces with fixed orthonormal bases. Write $\widehat R(n;\varepsilon)$ and $\widehat R^{\mathrm{cpp}}(n;\varepsilon)$ for the maximum unassisted and classical-post-processing assisted entanglement-transmission rates. A code has a positive integer message dimension $M$, rate $\log_2 M/n$, and squared fidelity to the normalized maximally entangled target at least $1-\varepsilon$. A cpp encoder may retain sender memory; its decoder is LOCC across that memory and the receiver outputs, with its final quantum output at the receiver and no preshared entanglement. Fix $0<\varepsilon<1$. All logarithms are binary and $\Phi^{-1}$ is the standard Gaussian quantile. Remainder constants may depend on the fixed channel and error, and are chosen before the block length: there are $C>0$ and $n_0\ge2$ such that the displayed bound holds for every integer $n\ge n_0$. Write $h(p)=-p\log_2p-(1-p)\log_2(1-p)$, with zero-weight terms zero, and $v(p)=p(\log_2p+h(p))^2+(1-p)(\log_2(1-p)+h(p))^2$. For the phase-flip channel $\mathcal Z_\gamma(X)=(1-\gamma)X+\gamma ZXZ$, assume $0<\gamma<1$ and $\gamma\ne1/2$. Then
--
--   $$\left|\widehat R_{\mathcal Z_\gamma}(n;\varepsilon)-\left(1-h(\gamma)+\sqrt{v(\gamma)/n}\,\Phi^{-1}(\varepsilon)+\frac{\log_2n}{2n}\right)\right|\le\frac Cn.$$
--
--   This gives the third-order operational boundary on the nonzero-dispersion domain.
-- source:
--   Quantum Coding with Finite Resources, arXiv:1504.04617v2, PDF p. 4, Result 1, Eq. (6)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Support50.P04

variable {A B E : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- arXiv:1504.04617v2, PDF pp.4,16–17, Result 1, Eq.(6).
Printed gamma in [0,1]; changed to positive nonzero dispersion, because the
+log2(n)/(2n) term is false at 0,1/2,1. Those printed cases are deferred separately. -/
theorem dephasing_thirdOrder (gamma epsilon : ℝ)
    (hg0 : 0 < gamma) (hg1 : gamma < 1) (hghalf : gamma ≠ 1/2)
    (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    thirdOrderExpansion (fun n => unassistedBoundary (QAlgorithms.Papers.Independent.Information100.P27.qubitDephasing (1-2*gamma)) n epsilon)
      (1-QAlgorithms.Papers.Independent.Frontier18.P07.binaryEntropyBits gamma) (binaryVariance gamma) epsilon := by sorry

end QAlgorithms.Papers.Independent.Support50.P04

end
