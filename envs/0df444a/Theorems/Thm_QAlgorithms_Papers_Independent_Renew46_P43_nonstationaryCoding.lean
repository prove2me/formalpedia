-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_nonstationaryCoding
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.nonstationaryCoding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:32:24.041747+00:00
-- url     : https://prove2.me/theorems/26af2979-2147-4023-835e-dae724f78dd7
-- title:
--   Theorem II.2: For 0<lambda<1, |log2 N(n,lambda)/n−sum_i C(Wi)/n|→0; C(Wi)=sup_P[H(PWi)−H(Wi|P)].
-- statement:
--   Fix a nonzero finite output system of dimension $d$. The nonstationary channels $W_i$ are nonempty measurable state sets; $C(W_i)=\sup_PI(P;W_i)$ optimizes over ALL probability laws on that set. A code has temporal product codewords, a collective block POVM with optional failure, positive length and a nonempty finite message set. $N(n,\lambda)$ optimizes actual codes under maximum error, with $0<\lambda<1$. In the maximal-code statements, $0<\tau<1$, the laws $P_i$ are arbitrary, and the measurable event $A$ has product mass at least $\tau$; constants $K',\delta>0$ are chosen before the channel, laws, event and length. In the converse $\epsilon>0$ and the threshold is uniform over channel sequences. The hybrid version uses intrinsic output trace and algebra-valued decoding.
--
--   $$
--   \left|\frac{\log_2N(n,\lambda)}n-\frac1n\sum_{i=1}^nC(W_i)\right|\longrightarrow0.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 24, Theorem II.2

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

/-- Theorem II.2, PDF p.24: absolute difference between operational rate and the
mean single-use capacities tends to zero for every fixed error in (0,1). -/
theorem nonstationaryCoding (d : ℕ) (hd : 0 < d) (W : ℕ → StateChannel (fullAlgebra d hd))
    (lambda : ℝ) (hlambda : 0 < lambda) (hsmall : lambda < 1) :
    Tendsto (fun n : ℕ => |Real.logb 2 (nonstationaryN W (n+1) lambda) / (n+1 : ℝ) -
      (∑ i : Fin (n+1), (W i.val).capacity) / (n+1 : ℝ)|) atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
