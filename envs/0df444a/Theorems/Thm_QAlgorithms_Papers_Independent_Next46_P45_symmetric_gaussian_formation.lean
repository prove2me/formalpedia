-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P45_symmetric_gaussian_formation
-- name    : QAlgorithms.Papers.Independent.Next46.P45.symmetric_gaussian_formation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:47:13.315818+00:00
-- url     : https://prove2.me/theorems/a517a4ae-e45a-4058-b4fb-53d1a0e86a4b
-- title:
--   Symmetric Gaussian entanglement of formation
-- statement:
--   Let $\sigma$ be an actual positive trace-class density operator of trace one on the full two-oscillator Fock space. Work in its chosen local Gaussian standard form, with arbitrary first moments and full anticommutator covariance $\Gamma=\operatorname{standard}(n,n,k_x,-k_p)$ in the order $(X_A,P_A,X_B,P_B)$, where $k_x\ge k_p\ge0$. The covariance is physically admissible: $\Gamma+i\Omega\succeq0$, and all first and second moments are finite. Use $[X_j,P_j]=i$, so the vacuum covariance is the identity. Set $d=\sqrt{(n-k_x)(n-k_p)}$ and $\bar d=\min\{1,d\}$. With logarithms in base two and $0\log_2 0=0$, define $c_\pm(t)=(t^{-1/2}\pm t^{1/2})^2/4$ and $f(t)=c_+(t)\log_2c_+(t)-c_-(t)\log_2c_-(t)$ for $0<t\le1$. Then
--
--   $$E_F(\sigma)=f(\bar d).$$
--
--   Here $E_F$ is the infimum of average reduced-state spectral entropy over all probability ensembles of normalized pure vectors with barycenter $\sigma$, including continuous and non-Gaussian ensembles. Thus the answer is $f(d)$ when $d<1$ and zero when $d\ge1$. This evaluates the unrestricted entanglement cost of forming a symmetric Gaussian state in one copy.
-- source:
--   Entanglement of formation for symmetric Gaussian states, arXiv:quant-ph/0304042v1, PDF p. 4, Proposition 2: entanglement of formation of symmetric two-mode Gaussian states

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P45

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P45

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (rankOne IsBarycenter)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov DensityKernel GaussianWithCovariance standardFormCovariance productWeyl
   CharacteristicSummable multimodeWeylTrace covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Claimed50.P35 (spectralEntropyBits InterleavedPhase)

local instance : MeasurableSpace TwoMode := borel TwoMode

/-- PDF p.4, Proposition 2, with (12)–(17), p.3. Boundary correction:
the printed f(d) suppresses separable d>=1, although f is defined only on (0,1].
The corrected all-symmetric-state result is f(min(1,d)). Actual physical Gaussian
density and full uncertainty positivity are in GaussianWithCovariance. -/
theorem symmetric_gaussian_formation
    (rho : DensityKernel 2) (n kx kp : ℝ) (hkp : 0 ≤ kp) (hk : kp ≤ kx)
    (hphysical : GaussianWithCovariance rho (standardFormCovariance n n kx (-kp))) :
    entanglementOfFormation rho = ENNReal.ofReal (gaussianFormationBits (symmetricEprLevel n kx kp)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P45

end
