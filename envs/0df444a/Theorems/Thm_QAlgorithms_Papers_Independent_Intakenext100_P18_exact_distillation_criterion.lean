-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P18_exact_distillation_criterion
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P18.exact_distillation_criterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:29:47.339802+00:00
-- url     : https://prove2.me/theorems/15c51508-32f5-458a-bb4e-22f477011eb9
-- title:
--   Exact single-copy distillation criterion
-- statement:
--   Let $N,M\ge1$ and $1\le m\le\min(N,M)$, and let $\rho$ be a positive trace-one operator on $\mathbb C^N\otimes\mathbb C^M$. Exact noncollective distillation means there are local contractions $A:\mathbb C^N\to\mathbb C^m$ and $B:\mathbb C^M\to\mathbb C^m$ such that the output has strictly positive trace and, after division by that trace, equals the normalized $m$-dimensional plus Bell projector $P_+^{(m)}$. Then
--
--   $$\rho\text{ is exactly noncollectively distillable to }P_+^{(m)}\iff\exists P,Q,\psi\ne0:\ (P\otimes Q)\rho(P\otimes Q)=|\psi\rangle\langle\psi|,$$
--
--   where $P,Q$ are orthogonal projections of ranks $m,m$ on the original local spaces and the coefficient matrix of $\psi$ has complex rank $m$. The vector $\psi$ need not be normalized.
--
--   This characterizes successful one-copy extraction. Rescaling a product operator to contractions does not affect its normalized output or whether its success is positive; the case $m=1$ is retained.
-- source:
--   General teleportation channel, singlet fraction and quasi-distillation, arXiv:quant-ph/9807091v2, PDF p. 10, §VI, Proposition 2: exact single-copy distillation criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P18

noncomputable section

open QAlgorithms MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Intakenext100.P18

open QAlgorithms.Papers.Independent.Claimed50.P28 (maximallyEntangledDensity)

open QAlgorithms.Papers.Independent.Support50.P11 (choiState teleportWeyl bellKet)

open QAlgorithms.Papers.Independent.Renew46.P40 (initialJoint)

/-- PDF pp.9--10, Proposition 2: exact one-copy extraction iff a rank-m
product projection leaves a nonzero pure positive operator of Schmidt rank m.
The vector on the right is deliberately not required to have norm one. -/
theorem exact_distillation_criterion (N M m : ℕ) (hN : 0 < N) (hM : 0 < M)
    (hm : 0 < m) (hmN : m ≤ N) (hmM : m ≤ M)
    (rho : Matrix (Fin N × Fin M) (Fin N × Fin M) ℂ) (hrho : IsDensityMatrix rho) :
    ExactlyDistillable rho m hm ↔
      ∃ P : Matrix (Fin N) (Fin N) ℂ, ∃ Q : Matrix (Fin M) (Fin M) ℂ,
      ∃ psi : EuclideanSpace ℂ (Fin N × Fin M),
        IsRankProjection m P ∧ IsRankProjection m Q ∧ psi ≠ 0 ∧
        Matrix.rank (fun i j => psi (i, j)) = m ∧
        conjSuperop (Matrix.kronecker P Q) rho = pureDensity psi := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P18

end
