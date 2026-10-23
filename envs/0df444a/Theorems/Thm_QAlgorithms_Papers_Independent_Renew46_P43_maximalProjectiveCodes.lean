-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_maximalProjectiveCodes
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.maximalProjectiveCodes
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:34:50.634532+00:00
-- url     : https://prove2.me/theorems/adf5194f-848f-4e78-b04f-2e872f513bf1
-- title:
--   Remark II.5: In II.4 all decoding effects Dm can be required to be projectors.
-- statement:
--   Fix a nonzero finite output system of dimension $d$. The nonstationary channels $W_i$ are nonempty measurable state sets; $C(W_i)=\sup_PI(P;W_i)$ optimizes over ALL probability laws on that set. A code has temporal product codewords, a collective block POVM with optional failure, positive length and a nonempty finite message set. $N(n,\lambda)$ optimizes actual codes under maximum error, with $0<\lambda<1$. In the maximal-code statements, $0<\tau<1$, the laws $P_i$ are arbitrary, and the measurable event $A$ has product mass at least $\tau$; constants $K',\delta>0$ are chosen before the channel, laws, event and length. In the converse $\epsilon>0$ and the threshold is uniform over channel sequences. The hybrid version uses intrinsic output trace and algebra-valued decoding.
--
--   $$
--   D_m^2=D_m,\quad f(m)\in A,\quad\operatorname{Tr}D_m\le\operatorname{Tr}\Pi_{H,f(m),\delta}^n,\quad\log_2|M|\ge\sum_iI(P_i;W_i)-K'\sqrt n.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 26, Remark II.5

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

/-- Remark II.5, PDF p.26: all II.4 conclusions with projective decoding effects.
The complementary failure effect completes the measurement. -/
theorem maximalProjectiveCodes (d : ℕ) (hd : 0 < d) (tau lambda : ℝ)
    (htau : 0 < tau) (htausmall : tau < 1) (hlambda : 0 < lambda) (hlambdasmall : lambda < 1) :
    ∃ K delta : ℝ, 0 < delta ∧ ∀ (n : ℕ), 0 < n →
      ∀ (W : ℕ → StateChannel (fullAlgebra d hd))
        (P : ∀ i : Fin n, ProbabilityMeasure (W i.val).carrier)
        (event : Set (∀ i : Fin n, (W i.val).carrier)), MeasurableSet event →
      ENNReal.ofReal tau ≤ (Measure.pi (fun i => (P i : Measure (W i.val).carrier))) event →
      MaximalCodeConclusion P event K delta lambda true := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
