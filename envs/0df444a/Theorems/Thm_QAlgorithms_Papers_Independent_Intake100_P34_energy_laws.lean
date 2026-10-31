-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P34_energy_laws
-- name    : QAlgorithms.Papers.Independent.Intake100.P34.energy_laws
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:18:15.663275+00:00
-- url     : https://prove2.me/theorems/fff68e4a-bb89-4466-ace7-3cec489adb01
-- title:
--   §3.5, (17)–(18) — first and second laws
-- statement:
--   Assume detailed balance, positivity improvement, and a common self-adjoint Hamiltonian $H$ with reservoir Gibbs states at inverse temperatures $\beta_j>0$. Let $F_j=L_j(H)$, $\phi_j=\rho_+(F_j)$ and $\bar s=-\nabla e(0)$. Then
--
--   $$\bar s_j=-\beta_j\phi_j,\qquad\sigma(\rho_+)=-\sum_j\beta_j\phi_j\ge0,\qquad\sum_j\phi_j=0.$$
--
--   The flux is out of a reservoir into the system. These are the second law and the steady first law, with the entropy/energy conversion fixed by that orientation.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, PDF p. 11, §3.5, (17)–(18)

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

/-- PDF p.11, (17)–(18): first and second laws, with flux out of each reservoir. -/
theorem energy_laws {d M : ℕ} (D : DBData d M) (hER : ER D)
    (H : Mat d) (beta : EntropyCoordinates M) (hThermal : Thermal D H beta) :
    (∀ j, entropyMean D j = -beta j * energyMean D H j) ∧
    reservoirEntropyProduction D (steadyDensity (reservoirGenerator D)) = ((-∑ j, beta j * energyMean D H j : ℝ) : EReal) ∧
    0 ≤ -∑ j, beta j * energyMean D H j ∧ ∑ j, energyMean D H j = 0 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P34

end
