-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P04_oneUse_testingRains
-- name    : QAlgorithms.Papers.Independent.Support50.P04.oneUse_testingRains
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:33:09.533999+00:00
-- url     : https://prove2.me/theorems/2c690a16-03bb-4493-ac27-4e7bf931cce1
-- title:
--   One-use testing-Rains metaconverse
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on finite positive-dimensional complex Hilbert spaces with fixed orthonormal bases. Write $\widehat R(n;\varepsilon)$ and $\widehat R^{\mathrm{cpp}}(n;\varepsilon)$ for the maximum unassisted and classical-post-processing assisted entanglement-transmission rates. A code has a positive integer message dimension $M$, rate $\log_2 M/n$, and squared fidelity to the normalized maximally entangled target at least $1-\varepsilon$. A cpp encoder may retain sender memory; its decoder is LOCC across that memory and the receiver outputs, with its final quantum output at the receiver and no preshared entanglement. Fix $0<\varepsilon<1$. For normalized $\rho$, let $\omega^\rho=(\mathrm{id}\otimes\mathcal N)(\psi^\rho)$ with the source first-factor purification. Define
--
--   $$I_R^\varepsilon(\mathcal N)=\sup_{\rho\in\mathcal S(A)}\inf_{\sigma\in\mathrm{PPT}^{\prime}}D_H^\varepsilon(\omega^\rho\|\sigma),$$
--
--   where $D_H^\varepsilon(\omega\|\sigma)=-\log_2\min\{\operatorname{tr}(T\sigma):0\preceq T\preceq I,\operatorname{tr}(T\omega)\ge1-\varepsilon\}$, with value $+\infty$ when its testing value is zero. Then
--
--   $$\widehat R^{\mathrm{cpp}}(1;\varepsilon)\le I_R^\varepsilon(\mathcal N).$$
--
--   The comparison state may vary with the input state.
-- source:
--   Quantum Coding with Finite Resources, arXiv:1504.04617v2, PDF p. 10, Lemma 1, Eq. (24)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Support50.P04

variable {A B E : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- arXiv:1504.04617v2, PDF pp.10–11, Lemma 1, Eq.(24).
The comparison state is optimized separately for each normalized channel input. -/
theorem oneUse_testingRains [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (epsilon : ℝ)
    (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    cppBoundary N 1 epsilon ≤ channelTestingRains N epsilon := by sorry

end QAlgorithms.Papers.Independent.Support50.P04

end
