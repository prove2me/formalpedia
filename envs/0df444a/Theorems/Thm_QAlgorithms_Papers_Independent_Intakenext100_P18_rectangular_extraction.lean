-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P18_rectangular_extraction
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P18.rectangular_extraction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:31:21.734633+00:00
-- url     : https://prove2.me/theorems/02ee3bcf-ea6d-4e9f-8867-3f73172f011b
-- title:
--   Exact extraction from a rectangular resource
-- statement:
--   Let $1\le N<M$, let $|\Phi_N\rangle=N^{-1/2}\sum_{i=0}^{N-1}|i\rangle_A|i\rangle_B$ in $\mathbb C^N\otimes\mathbb C^M$, and let $P$ be Bob's orthogonal projection onto his first $N$ coordinates. Let $\tau$ be a density operator whose Bob marginal obeys $P\operatorname{Tr}_A\tau=0$. For $0<p\le1$, put $\rho=p|\Phi_N\rangle\langle\Phi_N|+(1-p)\tau$. Then $\rho$ is a density, $I$ and $P$ are physical local contractions, and
--
--   $$(I\otimes P)\rho(I\otimes P)=p|\Phi_N\rangle\langle\Phi_N|.$$
--
--   The success probability is exactly $p$, and the conditional output is exactly the embedded plus state. In particular $\rho$ is exactly noncollectively distillable to the $N$-dimensional plus state. If $p<1$, $\rho$ is mixed (rank greater than one).
--
--   Only Bob's noise marginal is restricted; there is no extra condition on Alice's marginal. Strict positivity of $p$ excludes the inadmissible zero-success endpoint.
-- source:
--   General teleportation channel, singlet fraction and quasi-distillation, arXiv:quant-ph/9807091v2, PDF p. 10, §VI, unnumbered example: exact extraction from a rectangular resource

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P18

noncomputable section

open QAlgorithms MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Intakenext100.P18

open QAlgorithms.Papers.Independent.Claimed50.P28 (maximallyEntangledDensity)

open QAlgorithms.Papers.Independent.Support50.P11 (choiState teleportWeyl bellKet)

open QAlgorithms.Papers.Independent.Renew46.P40 (initialJoint)

/-- PDF p.10, rectangular example: Bob projects onto the first N coordinates.
Only Bob's noise marginal must be orthogonal. Success is exactly p>0.
For strict mixtures this is a mixed-state example, not a pure-state restatement. -/
theorem rectangular_extraction (N M : ℕ) (hN : 0 < N) (hNM : N < M)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (tau : Matrix (Fin N × Fin M) (Fin N × Fin M) ℂ) (htau : IsDensityMatrix tau)
    (horth : coordinateProjection N M * traceLeft tau = 0) :
    IsDensityMatrix (rectangularResource N M p tau) ∧
    IsLocalFilter (1 : Matrix (Fin N) (Fin N) ℂ) ∧
    IsLocalFilter (coordinateProjection N M) ∧
    (let omega := conjSuperop
      (Matrix.kronecker (1 : Matrix (Fin N) (Fin N) ℂ) (coordinateProjection N M))
      (rectangularResource N M p tau);
     omega = (p : ℂ) • rectangularPlus N M ∧ omega.trace.re = p ∧
     ((omega.trace.re)⁻¹ : ℂ) • omega = rectangularPlus N M) ∧
    ExactlyDistillable (rectangularResource N M p tau) N hN ∧
    (p < 1 → 1 < (rectangularResource N M p tau).rank) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P18

end
