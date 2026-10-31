-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P34_response_without_reversal
-- name    : QAlgorithms.Papers.Independent.Intake100.P34.response_without_reversal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:21:48.022371+00:00
-- url     : https://prove2.me/theorems/409fa8bb-4003-4219-9563-7a0428477353
-- title:
--   §3.6 Remarks 2–3 — response without time reversal
-- statement:
--   Retain the same positive-temperature thermal response family, open force neighborhood, fixed self-adjoint Hamiltonian, coordinatewise reservoir dependence, detailed balance, ER and continuous differentiability near zero, but impose no time reversal. With equilibrium density $\rho_0$ and currents $F_{0,j}$, the ordered corrected Green–Kubo formula still holds:
--
--   $$L_{jk}=-\int_0^\infty\rho_0(e^{tL_0}(F_{0,j})F_{0,k})\,dt+\tfrac{\delta_{jk}}2\rho_0(D_{0,j}(H,H)).$$
--
--   The equilibrium energy law satisfies the finite-mean-centered CLT on Gaussian continuity sets with covariance
--
--   $$D_{jk}=-\int_0^\infty\rho_0(e^{tL_0}(F_{0,j})F_{0,k}+e^{tL_0}(F_{0,k})F_{0,j})\,dt+\delta_{jk}\rho_0(D_{0,j}(H,H)).$$
--
--   This equals the energy-CGF Hessian and is positive semidefinite. The integrals converge absolutely. Onsager reciprocity is not asserted. These signs correct Remark 2 to agree with the earlier covariance identity.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, PDF p. 13, §3.6 Remarks 2–3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P34

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P34

open QAlgorithms (IsDensityMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P26 (Mat commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap IsPositiveMap)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P69 (Faithful)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Claimed50.P15
  (evaluate finiteRelativeEntropyNats entropyObservable)

open QAlgorithms.Papers.Independent.Claimed50.P43 (chaotic)

/-- PDF p.3: complex linear superoperators. -/
local notation "GeneratorMap" => fun d : ℕ => MatrixMap (Fin d) (Fin d)

/-- PDF pp.13–14, Remarks 2–3. All thermal, componentwise, ER and RE assumptions remain;
TR is removed. SOURCE CORRECTION: covariance is minus the symmetrized integrated correlation
plus local dissipation, consistently with (22). Green–Kubo remains ordered without Onsager. -/
theorem response_without_reversal {d M : ℕ} (F : ResponseFamily d M) :
    (∀ j k, IntegrableOn (energyCorrelation (equilibrium F) F.H j k) (Set.Ioi 0) ∧
      kinetic F j k = greenKubo F j k) ∧
    (∀ j k, coordinateHessianAtZero (responseCGF F 0) j k =
      -(∫ t in Set.Ioi (0 : ℝ), energyCorrelation (equilibrium F) F.H j k t +
        energyCorrelation (equilibrium F) F.H k j t) +
      (if j = k then evaluate (qdsGibbsDensity F.H F.beta0)
        (dissipation ((equilibrium F).generator j) F.H F.H) else 0)) ∧
    (∀ rho, IsDensityMatrix rho → HasCLT (energyLaw (equilibrium F) (fun _ => F.beta0) rho)
      (coordinateHessianAtZero (responseCGF F 0))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P34

end
