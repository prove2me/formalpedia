-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P34_linear_response
-- name    : QAlgorithms.Papers.Independent.Intake100.P34.linear_response
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:08:31.621682+00:00
-- url     : https://prove2.me/theorems/83fa64b4-05bb-4849-a406-899e9279bdfb
-- title:
--   Theorem 3.5 — linear response, corrected signs and CLT sets
-- statement:
--   Consider the thermal response family on an open neighborhood $U$ of $0\in\mathbb R^M$: a fixed self-adjoint $H$, inverse temperatures $\beta_j=\beta_0-\zeta_j>0$, $\beta_0>0$, detailed-balance summands depending only on their own force coordinate, positivity improvement of every total generator, and continuous differentiability near zero. Assume common componentwise time reversal for every member. Let $\rho_0=e^{-\beta_0H}/\operatorname{tr}(e^{-\beta_0H})$, $F_{0,j}=L_{0,j}(H)$, and $L_{jk}=\partial_{\zeta_k}\rho_{\zeta,+}(F_{\zeta,j})|_0$. Then the corrected Green–Kubo and Onsager formulas are
--
--   $$L_{jk}=-\int_0^\infty\rho_0(e^{tL_0}(F_{0,j})F_{0,k})\,dt+\frac{\delta_{jk}}2\rho_0(D_{0,j}(H,H)),\qquad L_{jk}=L_{kj}.$$
--
--   The integrals converge absolutely. The equilibrium energy law $Q^t_{\mathrm{eq},\rho}$ satisfies the positive-exponential transform $\int e^{t\alpha\cdot\phi}dQ^t=\operatorname{tr}(\rho e^{tL_{0,(\alpha/\beta_0)}}(1))$. For every initial state it obeys a central limit theorem, centered by its finite-time mean, on continuity sets of the centered Gaussian with covariance $D_{jk}=2L_{jk}$. This is the fluctuation-dissipation relation; the displayed Green–Kubo signs correct the printed force/flux inconsistency.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, PDF p. 13, Theorem 3.5

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

/-- PDF pp.12–14, Theorem 3.5. SOURCE CORRECTIONS: negative integrated correlation plus
positive half-dissipation in Green–Kubo, and Gaussian continuity sets in the CLT.
The displayed positive-exponential equilibrium transform is preserved. -/
theorem linear_response {d M : ℕ} (F : ResponseFamily d M)
    (hTR : ∀ z : F.U, TR (F.data z)) :
    (∀ j k, IntegrableOn (energyCorrelation (equilibrium F) F.H j k) (Set.Ioi 0) ∧
      kinetic F j k = greenKubo F j k) ∧
    (∀ j k, kinetic F j k = kinetic F k j) ∧
    (∀ rho, IsDensityMatrix rho →
      (∀ t : ℝ, 0 ≤ t → ∀ a : EntropyCoordinates M,
        Integrable (fun x => Real.exp (t * reservoirPairing a x)) (energyLaw (equilibrium F) (fun _ => F.beta0) rho t) ∧
        traceTransform (equilibrium F) rho t (countingParameterEmbedding (fun j => a j / F.beta0)) =
          ((∫ x, Real.exp (t * reservoirPairing a x) ∂(energyLaw (equilibrium F) (fun _ => F.beta0) rho t)) : ℂ)) ∧
      HasCLT (energyLaw (equilibrium F) (fun _ => F.beta0) rho) (2 • kinetic F)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P34

end
