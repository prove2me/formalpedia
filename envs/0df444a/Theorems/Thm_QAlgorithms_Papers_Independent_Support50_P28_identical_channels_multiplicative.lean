-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P28_identical_channels_multiplicative
-- name    : QAlgorithms.Papers.Independent.Support50.P28.identical_channels_multiplicative
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:15:56.493192+00:00
-- url     : https://prove2.me/theorems/08a49997-a222-457f-9977-010fef25e0f5
-- title:
--   Proposition 1, first clause: identical one-mode channels
-- statement:
--   Consider finitely many complete bosonic modes, with no photon cutoff or energy constraint. Covariances use the interleaved coordinates $(x_1,p_1,\ldots)$, $[x_j,p_j]=i$, and doubled vacuum covariance $I$. A centered Gaussian channel $\Phi_{X,Y}$ is an actual completely positive trace-preserving map, with covariance action $\gamma\mapsto X^T\gamma X+Y$ and $Y+i\sigma-iX^T\sigma X\ge0$, where $X,Y$ are real, $Y=Y^T$, and $\sigma=\bigoplus_j\left[\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right]$.
--
--   Write $\mathcal G$ for the normalized centered Gaussian densities and, for real $p>1$, put $\xi_p(\Phi)=\sup_{\rho\in\mathcal G}(\operatorname{Tr}\Phi(\rho)^p)^{1/p}$. For a finite channel family, multiplicativity means equality of the joint Gaussian-input supremum to the product of the factor suprema; joint inputs may be entangled.
--
--   Let $\Phi$ be any single-mode Gaussian channel, with singular signal or noise matrices allowed. For every integer $r\ge1$ and every real $p>1$,
--
--   $$\xi_p(\Phi^{\otimes r})=\xi_p(\Phi)^r.$$
--
--   This is precisely the first sentence of Proposition 1. The separate unrestricted optimizer-majorization sentence is deferred because the source's permitted singular cases can have an unattained supremum.
-- source:
--   Multiplicativity of maximal output purities of Gaussian channels under Gaussian inputs, arXiv:quant-ph/0406065v1, PDF p. 5, Proposition 1, first clause: identical one-mode channels

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P28

noncomputable section

open scoped BigOperators ENNReal ComplexOrder Matrix

namespace QAlgorithms.Papers.Independent.Support50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel rankOne)

open QAlgorithms.Papers.Independent.Claimed50.P47
  (Occupation gaussianStateCharacteristic singleCharacteristic weylKernel)

open QAlgorithms.Papers.Independent.Claimed50.P30 (phiMinus)

/-- PDF p.5, Proposition 1 FIRST SENTENCE ONLY: arbitrary identical channels,
including singular X and Y. The unrestricted second sentence is deferred. -/
theorem identical_channels_multiplicative (E : CenteredOscillatorChannel (Fin 1))
    (r : ℕ) (hr : 0 < r) (p : ℝ) (hp : 1 < p) :
    GaussianPurityMultiplicative p (m := fun _ : Fin r => 1) (fun _ => E) := by sorry

end QAlgorithms.Papers.Independent.Support50.P28

end
