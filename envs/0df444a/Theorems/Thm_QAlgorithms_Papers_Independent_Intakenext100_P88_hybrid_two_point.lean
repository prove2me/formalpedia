-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P88_hybrid_two_point
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P88.hybrid_two_point
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:29:48.165352+00:00
-- url     : https://prove2.me/theorems/b00d93b5-0268-46ca-b75d-bf540e41b6b9
-- title:
--   Hybrid preactivation two-point identity
-- statement:
--   Consider any hybrid layer at Gaussian initialization. Its incoming quantum outputs are $Q_{a j}=\langle U\phi(a),O_jU\phi(a)\rangle$, with normalized feature states and $m>0$ real-linearly independent Hermitian observables. The quantum circuit, features and observables may be drawn from an ensemble. Every $Q_{a j}$ is measurable and has finite fourth moment under the actual probability law. The classical preactivations are $C_{a r}=\sum_{j=1}^m W_{rj}Q_{a j}+b_r$. All real weights and biases are centered Gaussian, have independent coordinates, are jointly independent of the incoming quantum outputs, and satisfy $\operatorname{Var}(W_{rj})=C_W/m$ and $\operatorname{Var}(b_r)=C_b$, with $C_W,C_b\ge0$.
--
--   For all input data $a,b$ and classical output coordinates $r,s$,
--   $$
--   \mathbb E[C_{ar}C_{bs}]=\delta_{rs}\left(\frac{C_W}{m}\sum_{j=1}^m\mathbb E[Q_{aj}Q_{bj}]+C_b\right).
--   $$
--   Here $\delta_{rs}$ is the Kronecker delta. This is the covariance identity for the specified Gaussian mixing architecture; it is not a generalization or group-sector variance theorem.
-- source:
--   Representation Learning via Quantum Neural Tangent Kernels, arXiv:2111.04225v3, PDF p. 36, SM Eq.(196)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P88

open scoped BigOperators ComplexConjugate Topology NNReal ComplexOrder

open MeasureTheory ProbabilityTheory Filter

/-- PDF p.36 Eq.(196): two-point function of the affine preactivations under the actual
joint law. Independence and Gaussian centering are in HybridLayer; all moments exist. -/
theorem hybrid_two_point {Ω D R : Type*} [MeasurableSpace Ω] [Fintype R] [DecidableEq R]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {h L m : ℕ} {CW CB : ℝ≥0}
    (S : HybridLayer μ D R h L m CW CB) (a b : D) (r s : R) :
    (∫ w, preactivation S a r w * preactivation S b s w ∂μ) =
      kd r s * (((CW : ℝ) / (m : ℝ)) *
        (∑ j, ∫ w, incomingQuantumOutput S.quantum a j w * incomingQuantumOutput S.quantum b j w ∂μ) +
          (CB : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P88

end
