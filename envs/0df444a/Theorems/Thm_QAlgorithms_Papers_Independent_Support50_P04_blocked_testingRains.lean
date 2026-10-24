-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P04_blocked_testingRains
-- name    : QAlgorithms.Papers.Independent.Support50.P04.blocked_testingRains
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:34:23.395987+00:00
-- url     : https://prove2.me/theorems/16d77247-ae52-4ecc-906d-fceed97147e6
-- title:
--   Parallel n-use testing-Rains converse
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on finite positive-dimensional complex Hilbert spaces with fixed orthonormal bases. Write $\widehat R(n;\varepsilon)$ and $\widehat R^{\mathrm{cpp}}(n;\varepsilon)$ for the maximum unassisted and classical-post-processing assisted entanglement-transmission rates. A code has a positive integer message dimension $M$, rate $\log_2 M/n$, and squared fidelity to the normalized maximally entangled target at least $1-\varepsilon$. A cpp encoder may retain sender memory; its decoder is LOCC across that memory and the receiver outputs, with its final quantum output at the receiver and no preshared entanglement. Let $n\ge1$ and $0<\varepsilon<1$. For normalized $\rho$, let $\omega^\rho=(\mathrm{id}\otimes\mathcal N)(\psi^\rho)$ with the source first-factor purification. Define
--
--   $$I_R^\varepsilon(\mathcal N)=\sup_{\rho\in\mathcal S(A)}\inf_{\sigma\in\mathrm{PPT}^{\prime}}D_H^\varepsilon(\omega^\rho\|\sigma),$$
--
--   where $D_H^\varepsilon(\omega\|\sigma)=-\log_2\min\{\operatorname{tr}(T\sigma):0\preceq T\preceq I,\operatorname{tr}(T\omega)\ge1-\varepsilon\}$, with value $+\infty$ when its testing value is zero. Then
--
--   $$\widehat R^{\mathrm{cpp}}(n;\varepsilon)\le\frac1n I_R^\varepsilon(\mathcal N^{\otimes n}).$$
--
--   The blocked channel has arbitrary entangled inputs.
-- source:
--   Quantum Coding with Finite Resources, arXiv:1504.04617v2, PDF p. 11, Eq. (32)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Support50.P04

variable {A B E : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- arXiv:1504.04617v2, PDF p.11, Eq.(32).
Printed (32) omits 1/n; corrected by applying Lemma 1 to the actual blocked
channel and retaining Eq.(1)'s per-use rate. -/
theorem blocked_testingRains [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (n : ℕ) (hn : 0 < n)
    (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    cppBoundary N n epsilon ≤ channelTestingRains (piSuperop (fun _ : Fin n => N)) epsilon / (n : EReal) := by sorry

end QAlgorithms.Papers.Independent.Support50.P04

end
