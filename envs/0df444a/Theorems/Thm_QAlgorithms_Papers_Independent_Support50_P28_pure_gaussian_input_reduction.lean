-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P28_pure_gaussian_input_reduction
-- name    : QAlgorithms.Papers.Independent.Support50.P28.pure_gaussian_input_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:13:43.994511+00:00
-- url     : https://prove2.me/theorems/d1209d59-8e67-45e6-a373-98327ae266fd
-- title:
--   Lemma 1: pure Gaussian input reduction
-- statement:
--   Consider finitely many complete bosonic modes, with no photon cutoff or energy constraint. Covariances use the interleaved coordinates $(x_1,p_1,\ldots)$, $[x_j,p_j]=i$, and doubled vacuum covariance $I$. A centered Gaussian channel $\Phi_{X,Y}$ is an actual completely positive trace-preserving map, with covariance action $\gamma\mapsto X^T\gamma X+Y$ and $Y+i\sigma-iX^T\sigma X\ge0$, where $X,Y$ are real, $Y=Y^T$, and $\sigma=\bigoplus_j\left[\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right]$.
--
--   Write $\mathcal G$ for the normalized centered Gaussian densities and, for real $p>1$, put $\xi_p(\Phi)=\sup_{\rho\in\mathcal G}(\operatorname{Tr}\Phi(\rho)^p)^{1/p}$. For a finite channel family, multiplicativity means equality of the joint Gaussian-input supremum to the product of the factor suprema; joint inputs may be entangled.
--
--   Let $\Phi$ be any centered Gaussian channel on $n\ge1$ modes and let $p>1$ be real. Let $\widetilde{\mathcal G}$ be the centered pure Gaussian densities, where pure means the rank-one density of a unit vector. Then
--
--   $$\sup_{\rho\in\mathcal G}\|\Phi(\rho)\|_p=\sup_{\rho\in\widetilde{\mathcal G}}\|\Phi(\rho)\|_p.$$
--
--   This permits optimization over pure Gaussian inputs. It is an equality of suprema, with no assertion that either supremum is attained; no convexity of $\mathcal G$ is imposed.
-- source:
--   Multiplicativity of maximal output purities of Gaussian channels under Gaussian inputs, arXiv:quant-ph/0406065v1, PDF p. 4, Lemma 1: pure Gaussian input reduction

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

/-- PDF p.4, Lemma 1, (34): supremum reduction, with no optimizer assertion.
The channel's all-density law includes the displaced pure states in its proof. -/
theorem pure_gaussian_input_reduction {n : ℕ} (hn : 0 < n)
    (E : CenteredOscillatorChannel (Fin n)) (p : ℝ) (hp : 1 < p) :
    maximalOutputPurity p E.map = pureMaximalOutputPurity p E.map := by sorry

end QAlgorithms.Papers.Independent.Support50.P28

end
