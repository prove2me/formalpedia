-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_finiteChannelConverse
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.finiteChannelConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:41:10.715154+00:00
-- url     : https://prove2.me/theorems/936b1f00-4d1f-4cea-afc2-df7483762780
-- title:
--   Theorem II.17: Uniformly for all W,n and (n,lambda) codes: |M|≤(n+1)^a 2^(nC(W)+K(a,d,lambda)sqrt(n)); if constant composition P, |M|≤2^(nI(P;W)+
-- statement:
--   Let $a,d>0$ and $0<\lambda<1$. There is one real constant $K=K(a,d,\lambda)$ before the normalized finite channel $W$ and positive block length $n$. Codes have collective POVMs with optional failure and maximum message error at most $\lambda$; $N(n,\lambda)$ is their actual optimal message count. A fixed composition $P$ is required only for the explicitly strengthened clause.
--
--   $$
--   |M|\le(n+1)^a2^{nC(W)+K\sqrt n},\qquad |M|\le2^{nI(P;W)+K\sqrt n}\quad\text{if the code has composition }P.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 33, Theorem II.17

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

/-- Theorem II.17 and its explicit constant-composition strengthening, PDF p.33.
Composition is required only in the second clause. One K works for both clauses. -/
theorem finiteChannelConverse (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (lambda : ℝ) (hlambda : 0 < lambda) (hsmall : lambda < 1) :
    ∃ K : ℝ, ∀ (W : FiniteChannel a (fullAlgebra d hd)) (n : ℕ) (c : FiniteCode W n),
      c.error ≤ lambda →
      (c.messages : ℝ) ≤ (n+1 : ℝ)^a * exp2 (n * W.capacity + K * Real.sqrt n) ∧
      ∀ P : PMF (Fin a), c.Composition P →
        (c.messages : ℝ) ≤ exp2 (n * W.information P + K * Real.sqrt n) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
