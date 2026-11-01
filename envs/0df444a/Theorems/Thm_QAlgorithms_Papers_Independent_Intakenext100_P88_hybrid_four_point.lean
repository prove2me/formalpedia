-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P88_hybrid_four_point
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P88.hybrid_four_point
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:30:13.830728+00:00
-- url     : https://prove2.me/theorems/7d598ec0-f8b3-4522-b39e-91285d623b45
-- title:
--   Hybrid connected-four-point contraction identity
-- statement:
--   Consider any hybrid layer at Gaussian initialization. Its incoming quantum outputs are $Q_{a j}=\langle U\phi(a),O_jU\phi(a)\rangle$, with normalized feature states and $m>0$ real-linearly independent Hermitian observables. The quantum circuit, features and observables may be drawn from an ensemble. Every $Q_{a j}$ is measurable and has finite fourth moment under the actual probability law. The classical preactivations are $C_{a r}=\sum_{j=1}^m W_{rj}Q_{a j}+b_r$. All real weights and biases are centered Gaussian, have independent coordinates, are jointly independent of the incoming quantum outputs, and satisfy $\operatorname{Var}(W_{rj})=C_W/m$ and $\operatorname{Var}(b_r)=C_b$, with $C_W,C_b\ge0$.
--
--   Define $\kappa_C(1,2,3,4)=\mathbb E[C_1C_2C_3C_4]-\mathbb E[C_1C_2]\mathbb E[C_3C_4]-\mathbb E[C_1C_3]\mathbb E[C_2C_4]-\mathbb E[C_1C_4]\mathbb E[C_2C_3]$. In contrast, define $\Gamma_{ab,cd}(j,k)=\operatorname{Cov}(Q_{aj}Q_{bj},Q_{ck}Q_{dk})$, which subtracts only one product of pair moments.
--
--   For arbitrary data $a,b,c,d$ and classical coordinates $r,s,t,u$,
--   $$
--   \begin{aligned}
--   \kappa_C((a,r),(b,s),(c,t),(d,u))=\left(\frac{C_W}{m}\right)^2\Bigl(&\delta_{rs}\delta_{tu}\sum_{j,k}\Gamma_{ab,cd}(j,k)\\
--   &+\delta_{rt}\delta_{su}\sum_{j,k}\Gamma_{ac,bd}(j,k)\\
--   &+\delta_{ru}\delta_{st}\sum_{j,k}\Gamma_{ad,bc}(j,k)\Bigr).
--   \end{aligned}
--   $$
--   All sums run from $1$ to $m$. No diagonal-covariance hypothesis is needed for this exact contraction identity. It retains all covariance terms relevant to this architecture.
-- source:
--   Representation Learning via Quantum Neural Tangent Kernels, arXiv:2111.04225v3, PDF p. 38, SM Eqs.(197)-(201)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P88

open scoped BigOperators ComplexConjugate Topology NNReal ComplexOrder

open MeasureTheory ProbabilityTheory Filter

/-- PDF pp.37-38 Eqs.(197)-(201): exact connected-four-point contraction.
The quantum term is product covariance, not the four-variable quantum cumulant.
No orthogonality or diagonal covariance hypothesis is needed for this identity. -/
theorem hybrid_four_point {Ω D R : Type*} [MeasurableSpace Ω] [Fintype R] [DecidableEq R]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {h L m : ℕ} {CW CB : ℝ≥0}
    (S : HybridLayer μ D R h L m CW CB) (a b c d : D) (r s t u : R) :
    connectedFour μ (preactivation S a r) (preactivation S b s)
      (preactivation S c t) (preactivation S d u) = fourContraction S a b c d r s t u := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P88

end
