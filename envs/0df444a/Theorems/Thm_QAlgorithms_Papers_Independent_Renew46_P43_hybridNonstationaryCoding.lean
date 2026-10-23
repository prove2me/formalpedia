-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_hybridNonstationaryCoding
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.hybridNonstationaryCoding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:33:30.54043+00:00
-- url     : https://prove2.me/theorems/ea9f61bf-df7b-4fa2-b290-cea8ff166779
-- title:
--   Remark II.3: II.2 also holds with the output system replaced by an arbitrary finite *-subalgebra A.
-- statement:
--   Fix a nonzero finite output system of dimension $d$. The nonstationary channels $W_i$ are nonempty measurable state sets; $C(W_i)=\sup_PI(P;W_i)$ optimizes over ALL probability laws on that set. A code has temporal product codewords, a collective block POVM with optional failure, positive length and a nonempty finite message set. $N(n,\lambda)$ optimizes actual codes under maximum error, with $0<\lambda<1$. In the maximal-code statements, $0<\tau<1$, the laws $P_i$ are arbitrary, and the measurable event $A$ has product mass at least $\tau$; constants $K',\delta>0$ are chosen before the channel, laws, event and length. In the converse $\epsilon>0$ and the threshold is uniform over channel sequences. The hybrid version uses intrinsic output trace and algebra-valued decoding.
--
--   $$
--   \left|\frac{\log_2N(n,\lambda)}n-\frac1n\sum_{i=1}^nC(W_i)\right|\longrightarrow0\quad\text{for intrinsic output algebra }\mathcal A.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 24, Remark II.3

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

/-- Remark II.3, PDF p.24: the full nonstationary theorem also holds for a finite
intrinsic output algebra. Measurements and state restriction use that algebra's trace. -/
theorem hybridNonstationaryCoding (A : IntrinsicSystem) (W : ℕ → StateChannel A)
    (lambda : ℝ) (hlambda : 0 < lambda) (hsmall : lambda < 1) :
    Tendsto (fun n : ℕ => |Real.logb 2 (nonstationaryN W (n+1) lambda) / (n+1 : ℝ) -
      (∑ i : Fin (n+1), (W i.val).capacity) / (n+1 : ℝ)|) atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
