-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P04_dephasing_testing_converse
-- name    : QAlgorithms.Papers.Independent.Support50.P04.dephasing_testing_converse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:42:16.74412+00:00
-- url     : https://prove2.me/theorems/9ec46ccf-b0b3-49dc-b1d6-a127ef2bd6b5
-- title:
--   Dephasing finite-block quantum/classical testing converse
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on finite positive-dimensional complex Hilbert spaces with fixed orthonormal bases. Write $\widehat R(n;\varepsilon)$ and $\widehat R^{\mathrm{cpp}}(n;\varepsilon)$ for the maximum unassisted and classical-post-processing assisted entanglement-transmission rates. A code has a positive integer message dimension $M$, rate $\log_2 M/n$, and squared fidelity to the normalized maximally entangled target at least $1-\varepsilon$. A cpp encoder may retain sender memory; its decoder is LOCC across that memory and the receiver outputs, with its final quantum output at the receiver and no preshared entanglement. For $n\ge1$ and $0<\varepsilon<1$, let $P_\gamma(x,y)=(1-\gamma)/2$ when $x=y$ and $\gamma/2$ otherwise, for binary $x,y$, and let $Q(x,y)=1/4$. Classical testing is identified with diagonal density matrices. Assume $0\le\gamma\le1$ and set $\omega_\gamma=(1-\gamma)\phi^++\gamma\phi^-$ and $\sigma=(\phi^++\phi^-)/2$, where $\phi^\pm$ are the two phase Bell densities. Then
--
--   $$\widehat R_{\mathcal Z_\gamma}(n;\varepsilon)\le\widehat R^{\mathrm{cpp}}_{\mathcal Z_\gamma}(n;\varepsilon)\le\frac1nD_H^\varepsilon(\omega_\gamma^{\otimes n}\|\sigma^{\otimes n}),$$
--
--   $$D_H^\varepsilon(\omega_\gamma^{\otimes n}\|\sigma^{\otimes n})=D_H^\varepsilon(P_\gamma^{\times n}\|Q^{\times n}).$$
--
--   The equality identifies tests, not optimal code regions.
-- source:
--   Quantum Coding with Finite Resources, arXiv:1504.04617v2, PDF p. 16, Eqs. (61)–(63)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Support50.P04

variable {A B E : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- arXiv:1504.04617v2, PDF p.16, Eqs.(61)–(63): operational converse and exact
quantum-to-classical equality of tests; no equality of optimal coding regions. -/
theorem dephasing_testing_converse (gamma epsilon : ℝ)
    (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (n : ℕ) (hn : 0 < n) :
    let qtest := QAlgorithms.Papers.Independent.Dependency50.P36.testingEntropy (QAlgorithms.Papers.Independent.Information100.P60.copies n (choiState (QAlgorithms.Papers.Independent.Information100.P27.qubitDephasing (1-2*gamma))))
      (QAlgorithms.Papers.Independent.Information100.P60.copies n dephasingAlternative) epsilon
    let ctest := QAlgorithms.Papers.Independent.Dependency50.P36.testingEntropy (QAlgorithms.Papers.Independent.Information100.P60.copies n (bscJoint gamma)) (QAlgorithms.Papers.Independent.Information100.P60.copies n bscAlternative) epsilon
    unassistedBoundary (QAlgorithms.Papers.Independent.Information100.P27.qubitDephasing (1-2*gamma)) n epsilon ≤ cppBoundary (QAlgorithms.Papers.Independent.Information100.P27.qubitDephasing (1-2*gamma)) n epsilon ∧
    cppBoundary (QAlgorithms.Papers.Independent.Information100.P27.qubitDephasing (1-2*gamma)) n epsilon ≤ qtest / (n : EReal) ∧ qtest = ctest := by sorry

end QAlgorithms.Papers.Independent.Support50.P04

end
