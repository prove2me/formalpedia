-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P43_coefficient_rank_identification
-- name    : QAlgorithms.Papers.Independent.Intake100.P43.coefficient_rank_identification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:26:47.499471+00:00
-- url     : https://prove2.me/theorems/a8709ab9-67b4-4b32-a041-b5f70ab9827f
-- title:
--   Lemma 1: rank-preserving coefficient identification
-- statement:
--   Fix local computational bases of $H=\mathbb C^{d_A}\otimes\mathbb C^{d_B}$, where $1\le d_A\le d_B$, and an integer $1\le r\le d_A$. All subspaces and dimensions are complex. Write $\operatorname{Sch}(v)$ for the rank of the coefficient matrix of $v$. Subspace rank conditions concern every nonzero vector and do not require unit norm. The coefficient identification $C:H\to M_{d_A,d_B}(\mathbb C)$ is a complex linear equivalence, with $C(v)_{ij}=v_{ij}$ and
--
--   $$\operatorname{rank}C(v)=\operatorname{Sch}(v).$$
--
--   Its restriction is a bijection from the nonzero vectors of Schmidt rank $r$ onto matrices of rank $r$. This transfers the subspace problem to matrix rank; the rank-$r$ locus itself is not asserted to be linear.
-- source:
--   On the dimension of subspaces with bounded Schmidt rank, arXiv:0706.0705v1, PDF p. 2, Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P43

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intake100.P43

open QAlgorithms.Papers.Independent.Dependency50.P50 (Bipartite schmidtNumber)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

/-- PDF p.2, Lemma 1: the full coefficient map is linear and rank preserving;
its restriction to nonzero rank-r vectors is a set bijection, not a linear
space isomorphism of the rank-r locus. -/
theorem coefficient_rank_identification (dA dB r : ℕ)
    (hA : 0 < dA) (hAB : dA ≤ dB) (hr : 1 ≤ r) (hrA : r ≤ dA) :
    (∀ v : Bipartite dA dB, Matrix.rank (coefficientEquiv v) = schmidtNumber v) ∧
    Set.BijOn (coefficientEquiv (dA := dA) (dB := dB))
      {v | v ≠ 0 ∧ schmidtNumber v = r}
      {M | Matrix.rank M = r} := by sorry

end QAlgorithms.Papers.Independent.Intake100.P43

end
