-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P11_minEntropy_dimension
-- name    : QAlgorithms.Papers.Independent.Advance50.P11.minEntropy_dimension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:27:30.509933+00:00
-- url     : https://prove2.me/theorems/d38637e5-fe5b-4594-9c61-465e2d904ab1
-- title:
--   Dimension bound when discarding an unconditioned subsystem
-- statement:
--   All registers are finite dimensional and have positive dimension. Density operators are positive semidefinite with trace one, pure vectors have norm one, and logarithms are base two. Here $H_{\min}(\rho_{AB}\mid\sigma_B)$ is the fixed-reference min entropy, and $H_{\max}(\rho_{AB}\mid\sigma_B)$ is the historical support-rank max entropy, $\log_2\operatorname{tr}[(I_A\otimes\sigma_B)\Pi_{\rho_{AB}}]$, where $\Pi_\rho$ is the support projector. A conditioning register in place of a reference density means a supremum over normalized reference densities. Let $\rho_{ABR}$ be a density operator, $\rho_{AR}=\operatorname{tr}_B\rho_{ABR}$ its actual marginal, and $d_B=\dim B$. Then
--
--   $$
--   H_{\min}(\rho_{ABR}\mid R)\le H_{\min}(\rho_{AR}\mid R)+\log_2d_B.
--   $$
--
--   On the left the unconditioned system is $AB$, while the reference is only $R$.
--
--   This controls the change in optimized min entropy under disposal of an unconditioned register.
-- source:
--   Single-shot Quantum State Merging, arXiv:0912.4495v1, PDF p. 11, Lemma 3.9

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

/-- Lemma 3.9, PDF p.11, (3.13): B is UNCONDITIONED on the left; only B is traced out. -/
theorem minEntropy_dimension {A B R : Type} [Fintype A] [Fintype B] [Fintype R]
    [DecidableEq A] [DecidableEq B] [DecidableEq R] [Nonempty A] [Nonempty B] [Nonempty R]
    (rho : Matrix (R × (A × B)) (R × (A × B)) ℂ) (hrho : IsDensityMatrix rho) :
    optimizedMin (referenceLast rho) ≤ optimizedMin (marginalAR rho) +
      (Real.logb 2 (Fintype.card B) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P11

end
