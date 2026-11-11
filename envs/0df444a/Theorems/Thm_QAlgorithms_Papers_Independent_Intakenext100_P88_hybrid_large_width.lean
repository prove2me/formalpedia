-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P88_hybrid_large_width
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P88.hybrid_large_width
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-31T08:30:42.247126+00:00
-- url     : https://prove2.me/theorems/6f02a01d-756c-41c0-b1ed-67702ebb735d
-- title:
--   Non-Gaussianity from large quantum width
-- statement:
--   Consider any hybrid layer at Gaussian initialization. Its incoming quantum outputs are $Q_{a j}=\langle U\phi(a),O_jU\phi(a)\rangle$, with normalized feature states and $m>0$ real-linearly independent Hermitian observables. The quantum circuit, features and observables may be drawn from an ensemble. Every $Q_{a j}$ is measurable and has finite fourth moment under the actual probability law. The classical preactivations are $C_{a r}=\sum_{j=1}^m W_{rj}Q_{a j}+b_r$. All real weights and biases are centered Gaussian, have independent coordinates, are jointly independent of the incoming quantum outputs, and satisfy $\operatorname{Var}(W_{rj})=C_W/m$ and $\operatorname{Var}(b_r)=C_b$, with $C_W,C_b\ge0$.
--
--   Define $\kappa_C(1,2,3,4)=\mathbb E[C_1C_2C_3C_4]-\mathbb E[C_1C_2]\mathbb E[C_3C_4]-\mathbb E[C_1C_3]\mathbb E[C_2C_4]-\mathbb E[C_1C_4]\mathbb E[C_2C_3]$. In contrast, define $\Gamma_{ab,cd}(j,k)=\operatorname{Cov}(Q_{aj}Q_{bj},Q_{ck}Q_{dk})$, which subtracts only one product of pair moments.
--
--   Fix $C_W,C_b\ge0$ and a width-independent $B\ge0$ before choosing the width, data space or ensemble. Suppose, for every data quadruple and every $j,k$,
--   $$
--   |\Gamma_{ab,cd}(j,k)|\le B\delta_{jk}.
--   $$
--   The quantification includes all three data pairings. Then
--   $$
--   |\kappa_C((a,r),(b,s),(c,t),(d,u))|\le\frac{C_W^2B}{m}
--   (\delta_{rs}\delta_{tu}+\delta_{rt}\delta_{su}+\delta_{ru}\delta_{st})
--   \le\frac{3C_W^2B}{m}.
--   $$
--   Thus the connected classical four-point function is uniformly $O(1/m)$. This is a statement at initialization, applicable to each hybrid layer satisfying the hypotheses; it does not imply full Gaussian-process convergence or derivative suppression during training.
-- source:
--   Representation Learning via Quantum Neural Tangent Kernels, arXiv:2111.04225v3, PDF p. 8, Main Theorem 5; SM Eqs.(202)-(203)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P88

open scoped BigOperators ComplexConjugate Topology NNReal ComplexOrder

open MeasureTheory ProbabilityTheory Filter

/-- PDF p.8 Theorem 5, SM p.38 Eqs.(202)-(203): uniform 1/m suppression.
CW and B precede all widths and ensembles. Equation (203) prints Q on the left; it must
be C, as its preceding Eq.(200) and the contraction show. Only that label is corrected;
no Gaussian-process convergence or derivative/dynamical suppression is asserted. -/
theorem hybrid_large_width (CW CB : ℝ≥0) (B : ℝ) (hB : 0 ≤ B) :
    ∀ {Ω D R : Type*} [MeasurableSpace Ω] [Fintype R] [DecidableEq R]
      (μ : Measure Ω) [IsProbabilityMeasure μ] {h L m : ℕ}
      (S : HybridLayer μ D R h L m CW CB),
      (∀ (a b c d : D) (j k : Fin m),
        |productCovariance μ S.quantum a b c d j k| ≤ B * kd j k) →
      ∀ (a b c d : D) (r s t u : R),
        |connectedFour μ (preactivation S a r) (preactivation S b s)
          (preactivation S c t) (preactivation S d u)| ≤
        (CW : ℝ) ^ 2 * B / (m : ℝ) *
          (kd r s * kd t u + kd r t * kd s u + kd r u * kd s t) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P88

end
