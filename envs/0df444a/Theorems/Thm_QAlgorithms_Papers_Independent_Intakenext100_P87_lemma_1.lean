-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P87_lemma_1
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P87.lemma_1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:20:38.807024+00:00
-- url     : https://prove2.me/theorems/ff671877-5d17-4688-9608-5e744c59824b
-- title:
--   Supplementary Note 2, Lemma 1: high fidelity implies low entropy
-- statement:
--   Let $R\ge1$ and let $\rho$ be a positive semidefinite trace-one operator on the $R$ pairs. Entropy is measured in bits. Suppose $0<\delta<1-4^{-R}$ and the squared singlet overlap satisfies $\langle\Psi^-{}^{\otimes R}|\rho|\Psi^-{}^{\otimes R}\rangle>1-\delta$. Then
--
--   $$S(\rho)<-(1-\delta)\log_2(1-\delta)-\delta\log_2\!\left(\frac{\delta}{4^R-1}\right).$$
--
--   The explicit interval for $\delta$ is the increasing branch used in the source's maximum-entropy comparison, and the strict inequality matches the strict overlap assumption.
-- source:
--   Unconditional Security Of Quantum Key Distribution Over Arbitrarily Long Distances, arXiv:quant-ph/9803006v5, PDF p. 19, Supplementary Note 2, Lemma 1: high fidelity implies low entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P87

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P87

open scoped Matrix ComplexConjugate

open QAlgorithms.Measurements

/-- PDF p.19, Lemma 1: the proof uses the increasing entropy branch, here stated explicitly. -/
theorem lemma_1 (R : ℕ) (hR : 0 < R)
    (rho : Matrix (PairRegister R) (PairRegister R) ℂ) (hrho : IsDensityMatrix rho)
    (delta : ℝ) (hd : 0 < delta) (hsmall : delta < 1 - 1 / (2 : ℝ) ^ (2 * R))
    (hF : 1 - delta < singletOverlap rho) :
    vnEntropy rho < -(1 - delta) * Real.logb 2 (1 - delta) -
      delta * Real.logb 2 (delta / ((2 : ℝ) ^ (2 * R) - 1)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P87

end
