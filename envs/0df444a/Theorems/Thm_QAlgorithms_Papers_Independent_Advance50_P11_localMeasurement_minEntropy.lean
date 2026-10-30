-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P11_localMeasurement_minEntropy
-- name    : QAlgorithms.Papers.Independent.Advance50.P11.localMeasurement_minEntropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:35:30.29625+00:00
-- url     : https://prove2.me/theorems/87dee377-9669-40d7-9699-15b1563001e9
-- title:
--   Fine-grained local measurement monotonicity
-- statement:
--   All registers are finite dimensional and have positive dimension. Density operators are positive semidefinite with trace one, pure vectors have norm one, and logarithms are base two. Here $H_{\min}(\rho_{AB}\mid\sigma_B)$ is the fixed-reference min entropy, and $H_{\max}(\rho_{AB}\mid\sigma_B)$ is the historical support-rank max entropy, $\log_2\operatorname{tr}[(I_A\otimes\sigma_B)\Pi_{\rho_{AB}}]$, where $\Pi_\rho$ is the support projector. A conditioning register in place of a reference density means a supremum over normalized reference densities. Let $\rho_{AR},\sigma_R$ be density operators with $\operatorname{supp}\rho_R\subseteq\operatorname{supp}\sigma_R$. Let $\{M_x:A\to A\}_x$ be a complete measurement. Put $\omega_x=(M_x\otimes I_R)\rho_{AR}(M_x\otimes I_R)^{\dagger}$, $p_x=\operatorname{tr}\omega_x$, and retain the entire fine-grained outcome in an orthonormal register $X$. With $\rho'_{ARX}=\sum_x\omega_x\otimes\lvert x\rangle\langle x\rvert$ and $\rho_X=\sum_xp_x\lvert x\rangle\langle x\rvert$,
--
--   $$
--   H_{\min}(\rho_{AR}\mid\sigma_R)\ge H_{\min}(\rho'_{ARX}\mid\sigma_R\otimes\rho_X).
--   $$
--
--   A zero-weight branch is the zero matrix; no minimum over artificial normalized zero branches occurs.
--
--   The flag is determined by the actual measurement, not by an arbitrary decomposition of its averaged output.
-- source:
--   Single-shot Quantum State Merging, arXiv:0912.4495v1, PDF p. 23, Proposition 4.9

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

/-- Proposition 4.9, PDF pp.23--24, (4.31): the FULL fine-grained outcome is retained.
A single M_x per reported outcome is the p.6 measurement model; an erased Kraus
index or an unrelated convex decomposition is not an admissible replacement. -/
theorem localMeasurement_minEntropy {A R X : Type} [Fintype A] [Fintype R] [Fintype X]
    [DecidableEq A] [DecidableEq R] [DecidableEq X] [Nonempty A] [Nonempty R]
    (rho : Matrix (A × R) (A × R) ℂ) (sigma : Matrix R R ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportIncluded (traceLeft rho) sigma)
    (M : X → Matrix A A ℂ) (hcomplete : ∑ x, (M x)ᴴ * M x = 1) :
    conditionalMin (flaggedOutput M rho) (Matrix.kronecker sigma (outcomeState M rho)) ≤
      conditionalMin rho sigma := by sorry

end QAlgorithms.Papers.Independent.Advance50.P11

end
