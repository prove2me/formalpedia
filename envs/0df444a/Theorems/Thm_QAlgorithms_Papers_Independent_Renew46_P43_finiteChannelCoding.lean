-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_finiteChannelCoding
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.finiteChannelCoding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:39:49.281762+00:00
-- url     : https://prove2.me/theorems/6092c2bf-be1f-4f3d-832d-0242757304d9
-- title:
--   Theorem II.16: Uniformly for finite W and positive n: N(n,lambda)≥2^(nC(W)−K(a,d,lambda)sqrt(n)), 0<lambda<1.
-- statement:
--   Let $a,d>0$ and $0<\lambda<1$. There is one real constant $K=K(a,d,\lambda)$ before the normalized finite channel $W$ and positive block length $n$. Codes have collective POVMs with optional failure and maximum message error at most $\lambda$; $N(n,\lambda)$ is their actual optimal message count. A fixed composition $P$ is required only for the explicitly strengthened clause.
--
--   $$
--   N(n,\lambda)\ge2^{nC(W)-K(a,d,\lambda)\sqrt n}.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 32, Theorem II.16

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

/-- Theorem II.16, PDF pp.32-33: finite-block square-root correction, uniformly
over all channels and positive lengths at fixed alphabet and output dimensions. -/
theorem finiteChannelCoding (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (lambda : ℝ) (hlambda : 0 < lambda) (hsmall : lambda < 1) :
    ∃ K : ℝ, ∀ W : FiniteChannel a (fullAlgebra d hd), ∀ n : ℕ, 0 < n →
      (finiteN W n lambda : ℝ) ≥ exp2 (n * W.capacity - K * Real.sqrt n) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
