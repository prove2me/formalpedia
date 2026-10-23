-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_codePartition
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.codePartition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:49:54.736605+00:00
-- url     : https://prove2.me/theorems/5b977170-d3ca-4c9a-b024-1769e57e986c
-- title:
--   Theorem IV.10: For W,P and lambda,delta,eta>0, all n≥n0 admit m−1≤2^(n(H(P)−I(P;W)+3delta)) disjoint codebooks Ci, each (n,lambda) code of size≥2
-- statement:
--   Let $W:X\to\mathcal S(Y)$ be a finite classical-input channel, $P$ a law on $X$, and $\lambda,\delta,\eta>0$. Uniformly in $P,W$ at fixed alphabet and output dimension, all sufficiently large $n$ admit $k$ disjoint codebooks $C_i$, each with an actual collective maximum-error decoder of error at most $\lambda$. The choice $k=0$ is allowed.
--
--   $$
--   k\le2^{n(H(P)-I(P;W)+3\delta)},\quad |C_i|\ge2^{n(I(P;W)-2\delta)},\quad P^{\otimes n}\!\left(X^n\setminus\bigcup_{i=1}^kC_i\right)<\eta.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 53, Theorem IV.10

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

/-- Theorem IV.10, PDF p.53: disjoint large codebooks, each carrying an actual
maximum-error decoder. Zero codebooks are allowed, as needed when eta>1. -/
theorem codePartition (a : ℕ) (ha : 0 < a) (A : IntrinsicSystem)
    (lambda delta eta : ℝ) (hlambda : 0 < lambda) (hdelta : 0 < delta) (heta : 0 < eta) :
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ (W : FiniteChannel a A) (P : PMF (Fin a)) (n : ℕ), n0 ≤ n →
      ∃ k : ℕ, ∃ c : Fin k → FiniteCode W n,
      (k : ℝ) ≤ exp2 (n * (pmfEntropy P - W.information P + 3 * delta)) ∧
      (∀ i, (c i).error ≤ lambda ∧ Function.Injective (c i).word ∧
        ((c i).codebook.card : ℝ) ≥ exp2 (n * (W.information P - 2 * delta))) ∧
      (∀ i j, i ≠ j → Disjoint (c i).codebook (c j).codebook) ∧
      (∑ w ∈ (Finset.univ.filter fun w : Fin n → Fin a => ∀ i, w ∉ (c i).codebook),
        ∏ t, (P (w t)).toReal) < eta := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
