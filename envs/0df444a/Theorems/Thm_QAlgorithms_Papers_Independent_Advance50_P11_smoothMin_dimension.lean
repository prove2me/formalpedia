-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P11_smoothMin_dimension
-- name    : QAlgorithms.Papers.Independent.Advance50.P11.smoothMin_dimension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:30:43.366451+00:00
-- url     : https://prove2.me/theorems/42557d5d-ec20-4f17-8c58-fcb3d4e4ba45
-- title:
--   Dimension bound at the same normalized smoothing radius
-- statement:
--   All registers are finite dimensional and have positive dimension. Density operators are positive semidefinite with trace one, pure vectors have norm one, and logarithms are base two. Here $H_{\min}(\rho_{AB}\mid\sigma_B)$ is the fixed-reference min entropy, and $H_{\max}(\rho_{AB}\mid\sigma_B)$ is the historical support-rank max entropy, $\log_2\operatorname{tr}[(I_A\otimes\sigma_B)\Pi_{\rho_{AB}}]$, where $\Pi_\rho$ is the support projector. A conditioning register in place of a reference density means a supremum over normalized reference densities. The superscript $\epsilon$ denotes optimization over normalized density operators at half trace-norm distance at most $\epsilon$: a supremum for fixed-reference min entropy and an infimum for fixed-reference rank-max entropy, followed by a supremum over normalized reference densities when conditioning on a register. Let $\rho_{ABR}$ be a density operator, $\rho_{AR}=\operatorname{tr}_B\rho_{ABR}$, $d_B=\dim B$, and $\epsilon\ge0$. Then
--
--   $$
--   H_{\min}^{\epsilon}(\rho_{ABR}\mid R)\le H_{\min}^{\epsilon}(\rho_{AR}\mid R)+\log_2d_B.
--   $$
--
--   There is no restriction $\epsilon<1$.
--
--   The same radius is retained when discarding the unconditioned subsystem.
-- source:
--   Single-shot Quantum State Merging, arXiv:0912.4495v1, PDF p. 14, Lemma 3.17

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P11

open QAlgorithms MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Support50.P21
  (conditionalMin conditionalMax hMin hMax largestEigenvalue)

open QAlgorithms.Papers.Independent.Dependency50.P35 (elog supportRank tr)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC marginalAR)

open QAlgorithms.Papers.Independent.Information100.P22 (bell mixed)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 3.17, PDF pp.14--15, (3.38): same normalized half-trace radius on both sides. -/
theorem smoothMin_dimension {A B R : Type} [Fintype A] [Fintype B] [Fintype R]
    [DecidableEq A] [DecidableEq B] [DecidableEq R] [Nonempty A] [Nonempty B] [Nonempty R]
    (rho : Matrix (R × (A × B)) (R × (A × B)) ℂ) (hrho : IsDensityMatrix rho)
    (eps : ℝ) (heps : 0 ≤ eps) :
    normalizedSmoothMin eps (referenceLast rho) ≤ normalizedSmoothMin eps (marginalAR rho) +
      (Real.logb 2 (Fintype.card B) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P11

end
