-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_remark2_6
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.remark2_6
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T18:33:24.455486+00:00
-- url     : https://prove2.me/theorems/9e9cbbfe-c146-438e-ab01-a4ff80e6fcf2
-- title:
--   Polynomial bound on tensor-power spectral values
-- statement:
--   Let $\rho$ be a density operator on a nonzero finite-dimensional complex Hilbert space and let $n\ge1$. If $S_n$ is the set of distinct eigenvalues of $\rho^{\otimes n}$, including zero when present, then
--
--   $$|S_n|\le(n+1)^{\operatorname{rank}\rho}.$$
--
--   The bound counts values rather than multiplicities and supplies the polynomial spectral factors in the recovery argument.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 8, Remark 2.6

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Remark 2.6, Eq.52 (PDF p.8): includes the kernel eigenvalue zero. -/
theorem remark2_6 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho : Op I) (hrho : IsDensityMatrix rho) (n : ℕ) (hn : 0 < n) :
    (Finset.univ.image (ascEigenvalues (matrixPower rho n))).card ≤ (n+1)^rho.rank := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
