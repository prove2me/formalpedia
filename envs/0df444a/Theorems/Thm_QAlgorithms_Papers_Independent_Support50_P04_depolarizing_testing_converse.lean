-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P04_depolarizing_testing_converse
-- name    : QAlgorithms.Papers.Independent.Support50.P04.depolarizing_testing_converse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:44:21.394377+00:00
-- url     : https://prove2.me/theorems/b2ced82a-4ed1-41f1-9989-8e81d4df03dd
-- title:
--   Depolarizing finite-block testing converse
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on finite positive-dimensional complex Hilbert spaces with fixed orthonormal bases. Write $\widehat R(n;\varepsilon)$ and $\widehat R^{\mathrm{cpp}}(n;\varepsilon)$ for the maximum unassisted and classical-post-processing assisted entanglement-transmission rates. A code has a positive integer message dimension $M$, rate $\log_2 M/n$, and squared fidelity to the normalized maximally entangled target at least $1-\varepsilon$. A cpp encoder may retain sender memory; its decoder is LOCC across that memory and the receiver outputs, with its final quantum output at the receiver and no preshared entanglement. For $n\ge1$ and $0<\varepsilon<1$, let $P_\gamma(x,y)=(1-\gamma)/2$ when $x=y$ and $\gamma/2$ otherwise, for binary $x,y$, and let $Q(x,y)=1/4$. Classical testing is identified with diagonal density matrices. For $0\le\alpha\le1$, let $\mathcal D_\alpha(X)=(1-\alpha)X+\frac\alpha3(X_1XX_1+YXY+ZXZ)$, where $X_1,Y,Z$ are Pauli matrices. Let $\omega_\alpha$ have Bell weights $(1-\alpha,\alpha/3,\alpha/3,\alpha/3)$ and let $\sigma$ have weights $(1/2,1/6,1/6,1/6)$. The latter is a normalized member of $\mathrm{PPT}^{\prime}$. Then
--
--   $$\widehat R_{\mathcal D_\alpha}(n;\varepsilon)\le\widehat R_{\mathcal D_\alpha}^{\mathrm{cpp}}(n;\varepsilon)\le\frac1nD_H^\varepsilon(\omega_\alpha^{\otimes n}\|\sigma^{\otimes n}),$$
--
--   $$D_H^\varepsilon(\omega_\alpha^{\otimes n}\|\sigma^{\otimes n})=D_H^\varepsilon(P_\alpha^{\times n}\|Q^{\times n}).$$
--
--   This is a shared testing upper bound; it does not compare the two exact operational channel boundaries.
-- source:
--   Quantum Coding with Finite Resources, arXiv:1504.04617v2, PDF p. 19, Eq. (73)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Support50.P04

variable {A B E : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- arXiv:1504.04617v2, PDF p.19, Eqs.(71)–(73): fixed normalized PPT Bell
alternative and the finite-block testing converse, with the source alpha/3 convention.
This is not the stronger printed operational comparison deferred under Result 3. -/
theorem depolarizing_testing_converse (alpha epsilon : ℝ)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (n : ℕ) (hn : 0 < n) :
    IsDensityMatrix depolarizingAlternative ∧ QAlgorithms.Papers.Independent.Dependency50.P36.pptPrime depolarizingAlternative ∧
    unassistedBoundary (QuditFidelity.depolarizingMap 2 (by norm_num) (4*alpha/3)) n epsilon ≤ cppBoundary (QuditFidelity.depolarizingMap 2 (by norm_num) (4*alpha/3)) n epsilon ∧
    cppBoundary (QuditFidelity.depolarizingMap 2 (by norm_num) (4*alpha/3)) n epsilon ≤
      QAlgorithms.Papers.Independent.Dependency50.P36.testingEntropy (QAlgorithms.Papers.Independent.Information100.P60.copies n (choiState (QuditFidelity.depolarizingMap 2 (by norm_num) (4*alpha/3))))
        (QAlgorithms.Papers.Independent.Information100.P60.copies n depolarizingAlternative) epsilon / (n : EReal) ∧
    QAlgorithms.Papers.Independent.Dependency50.P36.testingEntropy (QAlgorithms.Papers.Independent.Information100.P60.copies n (choiState (QuditFidelity.depolarizingMap 2 (by norm_num) (4*alpha/3))))
        (QAlgorithms.Papers.Independent.Information100.P60.copies n depolarizingAlternative) epsilon =
      QAlgorithms.Papers.Independent.Dependency50.P36.testingEntropy (QAlgorithms.Papers.Independent.Information100.P60.copies n (bscJoint alpha)) (QAlgorithms.Papers.Independent.Information100.P60.copies n bscAlternative) epsilon := by sorry

end QAlgorithms.Papers.Independent.Support50.P04

end
