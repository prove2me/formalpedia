-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P49_b2NoFiniteSingleModeGaussianDilation
-- name    : QAlgorithms.Papers.Independent.Claimed50.P49.b2NoFiniteSingleModeGaussianDilation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:09:24.718307+00:00
-- url     : https://prove2.me/theorems/29f97d59-aff5-45e9-b8ff-53a0e504037a
-- title:
--   No finite thermal linear one-mode dilation of noisy B2
-- statement:
--   Fix $N_0>0$. Take any bounded unitary on two full Bosonic modes implementing a real symplectic linear transformation $M$, and any thermal environment density with finite parameter $N\ge0$. Its operational receiver cannot have the $B_2$ data
--
--   $$K=I,\qquad\alpha=N_0I,\qquad m=0.$$
--
--   The obstruction is limited to linear Gaussian couplings with a single thermal environmental mode. It asserts nothing against arbitrary non-Gaussian dilations. An infinite-temperature formal limit is not a density and is not included.
-- source:
--   One-mode Bosonic Gaussian channels: a full weak-degradability classification, arXiv:quant-ph/0609013v2, PDF p. 13, §2.5; (2.23)–(2.25)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P49

noncomputable section

open scoped BigOperators ENNReal Topology

open Filter MeasureTheory

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

namespace QAlgorithms.Papers.Independent.Claimed50.P49

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Equations (2.23)-(2.25), PDF pp.13-14: obstruction only for finite-thermal,
linear Gaussian single-environment dilations. Arbitrary non-Gaussian dilations
are not excluded. The strict N0>0 guard excludes the identity. -/
theorem b2NoFiniteSingleModeGaussianDilation (N0 : ℝ) (hN0 : 0 < N0)
    (U : JointUnitary) (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : ImplementsJointGaussian U M)
    (sigma : State ℕ) (N : ℝ) (hthermal : IsThermal sigma.coefficients N) :
    ¬ IsGaussianChannel (dilationReceiver U sigma.coefficients) (canonicalData .B2 0 N0) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P49

end
