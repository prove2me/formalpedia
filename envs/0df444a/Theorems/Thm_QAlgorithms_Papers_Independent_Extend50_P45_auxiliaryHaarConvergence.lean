-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P45_auxiliaryHaarConvergence
-- name    : QAlgorithms.Papers.Independent.Extend50.P45.auxiliaryHaarConvergence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:06:55.512686+00:00
-- url     : https://prove2.me/theorems/a59d1e57-a648-4357-99d2-85e8ab4f37ab
-- title:
--   Frobenius Wasserstein convergence of the auxiliary walk
-- statement:
--   For $n\ge1$, let $\mu_{\rm Cl}$ be uniform sampling of the entire global $n$-qubit Clifford group modulo scalar phase, and let $\mu_{H,1}$ be Haar $U(2)$ on the first qubit. Set $\sigma=\mu_{\rm Cl}*\mu_{H,1}*\mu_{\rm Cl}$, with independent factors. Scalar phases of Clifford representatives are absorbed by the single-qubit Haar law. Let $W_{F,2}$ be the infimum over probability couplings $(X,Y)$ of $(\mathbb E\|X-Y\|_F^2)^{1/2}$, using the Frobenius chord metric on unitary matrices. For every integer $n\ge1$ and $k\ge1$,
--   $$W_{F,2}(\sigma^{*k},\mu_H)\le\left(1-\frac3{2^{2n}-1}\right)^{k/2}\pi\,2^{n/2}.$$
--   This states the printed convergence estimate, retaining its $\pi$ prefactor. At $n=1$, the walk itself is Haar and the right-hand side is zero.
-- source:
--   Random quantum circuits are approximate unitary $t$-designs in depth $O\left(nt^{5+o(1)}\right)$, arXiv:2203.16571v3, PDF p. 10, Lemma 5: Haar convergence of auxiliary Clifford/Haar walk, Eq.(31)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45

noncomputable section

open MeasureTheory

open scoped ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Extend50.P45

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixBorel

/-- PDF p.10, Lemma 5, Eq.(31): the printed pi prefactor is retained.
The metric is Frobenius chord Wasserstein-2. At n=1, sigma is Haar and k>=1. -/
theorem auxiliaryHaarConvergence (n k : ℕ) [Fintype (Clifford.ProjectiveGroup n)]
    (hn : 1 ≤ n) (hk : 1 ≤ k) :
    frobeniusWasserstein (steps (auxiliaryLaw n) k) (haarLaw n) ≤
      (1 - 3 / ((2 : ℝ) ^ (2 * n) - 1)) ^ ((k : ℝ) / 2) *
        Real.pi * (2 : ℝ) ^ ((n : ℝ) / 2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P45

end
