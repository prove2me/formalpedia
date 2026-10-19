-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P32_timeAverageDephasing
-- name    : QAlgorithms.Papers.Independent.Information100.P32.timeAverageDephasing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:44:58.541415+00:00
-- url     : https://prove2.me/theorems/f5714088-3480-4507-abd6-311fef33c078
-- title:
--   Time-averaged phase rotations implement complete dephasing
-- statement:
--   Work in arbitrary finite nonempty system and ancillary Hilbert spaces with fixed orthonormal reference bases. Write $\mathcal D(X)_{ij}=\delta_{ij}X_{ii}$ for complete dephasing in the specified basis. A density matrix is positive semidefinite with trace one; a channel is completely positive and trace preserving. Population–coherence decoupling means that diagonal and zero-diagonal operator sectors are each invariant, on all operators. Let $Z=\operatorname{diag}(z_i)$ have distinct real eigenvalues. For every density matrix $\rho$,
--   $$\lim_{T\to+\infty}\frac1{2T}\int_{-T}^T e^{-itZ}\rho e^{itZ}\,dt=\mathcal D(\rho).$$
--   The finite-interval matrix-valued integrands are continuous. Nondegeneracy ensures complete, rather than block, dephasing.
-- source:
--   Coherence -assisted quantum state preparation and thermal control through repeated interactions, arXiv:2610.10794v1, PDF p. 18, Appendix A.3 Eqs.(A24)–(A31): time-average dephasing representation

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

section

open scoped Matrix.Norms.Elementwise

/-- PDF pp.17–18, Eqs.(A24)–(A31): nondegeneracy removes every off-diagonal
entry; finite-interval integrands are continuous. A26's missing time factor is restored. -/
theorem timeAverageDephasing {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (z : I → ℝ) (hz : Function.Injective z) (r : Op I) (hr : IsDensityMatrix r) :
    Tendsto (fun t : ℝ => (2 * t)⁻¹ •
      ∫ s in (-t)..t, evolution (Matrix.diagonal fun i => (z i : ℂ)) s * r * (evolution (Matrix.diagonal fun i => (z i : ℂ)) s).conjTranspose)
      atTop (𝓝 (diagonal r)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P32

end
