-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P34_response_constraints
-- name    : QAlgorithms.Papers.Independent.Intake100.P34.response_constraints
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:20:56.583221+00:00
-- url     : https://prove2.me/theorems/72ed3a2e-8f3a-4f66-bb39-ece83859a070
-- title:
--   §3.6, (24)–(26) — transport constraints and combined symmetry
-- statement:
--   For the thermal, componentwise, continuously differentiable response family on an open neighborhood of zero, assume ER and common time reversal at every force. Let $L_{jk}$ be the derivative of the actual steady energy flux with respect to $\zeta_k=\beta_0-\beta_k$. Its columns sum to zero and its real quadratic form is nonnegative:
--
--   $$\sum_jL_{jk}=0,\qquad\sum_{j,k}x_jL_{jk}x_k\ge0.$$
--
--   For the positive-Laplace function $\chi(\zeta,\alpha)=e(\zeta,\alpha/\beta)$ and negative-Laplace function $g(\zeta,\alpha)=\chi(\zeta,-\alpha)$,
--
--   $$\chi(\zeta,\alpha)=\chi(\zeta,-\zeta-\alpha),\qquad g(\zeta,\alpha)=g(\zeta,\zeta-\alpha),$$
--
--   $$L_{jk}=\partial_{\zeta_k}\partial_{\alpha_j}\chi(0,0)=\tfrac12\partial_{\alpha_k}\partial_{\alpha_j}\chi(0,0),\qquad\partial_{\zeta_k}\partial_{\alpha_j}g(0,0)=-L_{jk}=-\tfrac12\partial_{\alpha_k}\partial_{\alpha_j}g(0,0).$$
--
--   Semidefiniteness corrects the printed strict definiteness, which is incompatible with the conservation zero mode. Distinguishing the two Laplace conventions resolves the printed derivative-sign conflict.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, PDF p. 13, §3.6, (24)–(26)

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

/-- PDF pp.12–13, (24)–(26). SOURCE CORRECTIONS: the quadratic form is semidefinite,
with the all-ones zero mode. Positive-Laplace chi obeys chi(z,a)=chi(z,-z-a);
negative-Laplace g obeys g(z,a)=g(z,z-a). Their mixed derivatives have opposite signs. -/
theorem response_constraints {d M : ℕ} (F : ResponseFamily d M)
    (hTR : ∀ z : F.U, TR (F.data z)) :
    (∀ k, ∑ j, kinetic F j k = 0) ∧
    (∀ x : EntropyCoordinates M, 0 ≤ ∑ j, ∑ k, x j * kinetic F j k * x k) ∧
    (∀ z ∈ F.U, ∀ a : EntropyCoordinates M,
      responseCGF F z a = responseCGF F z (fun j => -z j - a j) ∧
      negativeResponseCGF F z a = negativeResponseCGF F z (fun j => z j - a j)) ∧
    (∀ j k,
      kinetic F j k = countingCoordinateDerivative (fun z => countingCoordinateDerivative (responseCGF F z) j 0) k 0 ∧
      kinetic F j k = (1 / 2 : ℝ) * coordinateHessianAtZero (responseCGF F 0) j k ∧
      countingCoordinateDerivative (fun z => countingCoordinateDerivative (negativeResponseCGF F z) j 0) k 0 = -kinetic F j k ∧
      countingCoordinateDerivative (fun z => countingCoordinateDerivative (negativeResponseCGF F z) j 0) k 0 =
        -(1 / 2 : ℝ) * coordinateHessianAtZero (negativeResponseCGF F 0) j k) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P34

end
