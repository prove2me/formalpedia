-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_nonstationaryStrongConverse
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.nonstationaryStrongConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:35:44.10783+00:00
-- url     : https://prove2.me/theorems/128d848f-6db6-4452-bcdd-21cc73888dc5
-- title:
--   Theorem II.7: For fixed d, every 0<lambda<1,epsilon>0 admit n0 uniformly for all nonstationary channels: n≥n0 implies log2 N(n,lambda)≤sum_i C(W
-- statement:
--   Fix a nonzero finite output system of dimension $d$. The nonstationary channels $W_i$ are nonempty measurable state sets; $C(W_i)=\sup_PI(P;W_i)$ optimizes over ALL probability laws on that set. A code has temporal product codewords, a collective block POVM with optional failure, positive length and a nonempty finite message set. $N(n,\lambda)$ optimizes actual codes under maximum error, with $0<\lambda<1$. In the maximal-code statements, $0<\tau<1$, the laws $P_i$ are arbitrary, and the measurable event $A$ has product mass at least $\tau$; constants $K',\delta>0$ are chosen before the channel, laws, event and length. In the converse $\epsilon>0$ and the threshold is uniform over channel sequences. The hybrid version uses intrinsic output trace and algebra-valued decoding.
--
--   $$
--   \forall n\ge n_0(d,\lambda,\epsilon),\ \forall(W_i):\quad\log_2N(n,\lambda)\le\sum_{i=1}^n C(W_i)+n\epsilon.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 26, Theorem II.7

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

/-- Theorem II.7, PDF pp.26-28: one threshold for every channel sequence, after
fixing output dimension and the two tolerances. -/
theorem nonstationaryStrongConverse (d : ℕ) (hd : 0 < d)
    (lambda epsilon : ℝ) (hlambda : 0 < lambda) (hsmall : lambda < 1) (hepsilon : 0 < epsilon) :
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ n : ℕ, n0 ≤ n →
      ∀ W : ℕ → StateChannel (fullAlgebra d hd),
      Real.logb 2 (nonstationaryN W n lambda) ≤
        (∑ i : Fin n, (W i.val).capacity) + n * epsilon := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
