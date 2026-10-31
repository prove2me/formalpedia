-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P43_highly_mixed_square_states
-- name    : QAlgorithms.Papers.Independent.Intake100.P43.highly_mixed_square_states
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:33:58.06335+00:00
-- url     : https://prove2.me/theorems/64872cee-8609-4539-8c82-dd9e682a3b90
-- title:
--   Highly mixed square states with large Schmidt measure
-- statement:
--   Fix a real fraction $0<p\le1$ and any positive integer $d$. There is a nonzero complex subspace $S\subseteq\mathbb C^d\otimes\mathbb C^d$ such that, with $N=\dim_{\mathbb C}S$ and $\rho=P_S/N$, the operator $\rho$ is a density matrix admitting pure-state ensembles and
--
--   $$\operatorname{rank}\rho=N\ge p^2d^2,\qquad \operatorname{SchmidtMeasure}(\rho)\ge(1-p)d,$$
--
--   $$S_2(\rho)=\log_2 N\ge2\log_2d+2\log_2p.$$
--
--   Here $S_2$ is von Neumann entropy in bits, and Schmidt measure is the least achievable maximum component rank. The result holds for every positive $d$, hence for arbitrarily large systems; $p=1$ permits the maximally mixed state. The entropy parenthesis is interpreted as a lower bound because the projector rank is integral.
-- source:
--   On the dimension of subspaces with bounded Schmidt rank, arXiv:0706.0705v1, PDF p. 4, Discussion, highly mixed square states

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P43

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intake100.P43

open QAlgorithms.Papers.Independent.Dependency50.P50 (Bipartite schmidtNumber)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

/-- PDF p.4, highly mixed square states. The physical fraction is 0<p<=1.
The source's entropy parenthesis is a LOWER bound: exact entropy is log2(dim S),
since dimension is integral. This construction works for every positive d,
and hence for arbitrarily large d. At p=1 it includes the maximally mixed state. -/
theorem highly_mixed_square_states (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (d : ℕ) (hd : 0 < d) :
    ∃ S : Submodule ℂ (Bipartite d d),
      0 < Module.finrank ℂ S ∧
      QAlgorithms.IsDensityMatrix (normalizedProjector S) ∧
      (∃ E : PureEnsemble (Fin d × Fin d),
        QAlgorithms.ensembleDensity E.weight E.vector = normalizedProjector S) ∧
      Matrix.rank (normalizedProjector S) = Module.finrank ℂ S ∧
      p ^ 2 * (d : ℝ) ^ 2 ≤ (Matrix.rank (normalizedProjector S) : ℝ) ∧
      QAlgorithms.vnEntropy (normalizedProjector S) =
        Real.logb 2 (Module.finrank ℂ S : ℝ) ∧
      2 * Real.logb 2 (d : ℝ) + 2 * Real.logb 2 p ≤
        QAlgorithms.vnEntropy (normalizedProjector S) ∧
      (1 - p) * (d : ℝ) ≤ (schmidtMeasure (normalizedProjector S) : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P43

end
