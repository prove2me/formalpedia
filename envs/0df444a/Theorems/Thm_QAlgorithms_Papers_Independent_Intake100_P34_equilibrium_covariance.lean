-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P34_equilibrium_covariance
-- name    : QAlgorithms.Papers.Independent.Intake100.P34.equilibrium_covariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:20:04.712455+00:00
-- url     : https://prove2.me/theorems/89736874-aac0-45e9-8a70-07e601e01cb9
-- title:
--   §3.5, (22)–(23) — equilibrium covariance and time symmetry
-- statement:
--   Assume detailed balance and positivity improvement, with all reservoirs at one inverse temperature $\beta_0>0$ for a self-adjoint $H$. Then $\rho_+=\rho_0=e^{-\beta_0H}/\operatorname{tr}(e^{-\beta_0H})$, every reservoir fixes $\rho_0$, every steady energy flux vanishes, and $J_j^+=J_j=I_j=\beta_0F_j$, where $F_j=L_j(H)$. The equilibrium correlations are real and absolutely integrable. For the positive-Laplace energy cumulant function,
--
--   $$\partial_k\partial_j\chi(0)=-\int_0^\infty\rho_0(e^{tL}(F_j)F_k+e^{tL}(F_k)F_j)\,dt+\delta_{jk}\rho_0(D_j(H,H)).$$
--
--   For any reversal $\Theta$ of the total pair $(\rho_0,L)$ which fixes every current $F_j$, and every $t\ge0$,
--
--   $$\rho_0(e^{tL}(F_j)F_k)=\rho_0(\Theta(F_ke^{tL}(F_j)))=\rho_0(F_ke^{tL^{\rho_0}}(F_j))=\rho_0(e^{tL}(F_k)F_j).$$
--
--   Here $L^{\rho_0}(X)=L^*(X\rho_0)\rho_0^{-1}$ is the adjoint for $\operatorname{tr}(\rho_0X^*Y)$. Explicit current invariance corrects the printed total-pair-only condition and is weaker than common componentwise reversal. The covariance formula itself requires no reversal.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, PDF p. 12, §3.5, (22)–(23)

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

/-- PDF pp.11–12, (22)–(23): equilibrium covariance needs no reversal.
SOURCE CORRECTION: the printed total-pair TRI condition omits invariance of each current;
add exactly Theta(F_j)=F_j, the input supplied by the preceding componentwise-TR argument.
Total TRI alone allows asymmetric cross-correlations in a degenerate energy space.
The third expression retains the printed weighted-adjoint evolution exp(t L^{rho_0}). -/
theorem equilibrium_covariance {d M : ℕ} (D : DBData d M) (hER : ER D)
    (H : Mat d) (beta0 : ℝ) (hBeta : 0 < beta0)
    (hThermal : Thermal D H (fun _ => beta0)) :
    steadyDensity (reservoirGenerator D) = qdsGibbsDensity H beta0 ∧
    (∀ j, StationaryDensity (D.generator j) (qdsGibbsDensity H beta0) ∧ energyMean D H j = 0 ∧
      adjointCurrent D j = centeredCurrent D j ∧ centeredCurrent D j = entropyFlux D j ∧
      entropyFlux D j = (beta0 : ℂ) • energyFlux D H j) ∧
    (∀ j k, IntegrableOn (energyCorrelation D H j k) (Set.Ioi 0) ∧
      (∀ t : ℝ, 0 ≤ t →
        expect (qdsGibbsDensity H beta0) (qdsEvolution (reservoirGenerator D) t (energyFlux D H j) * energyFlux D H k) =
          (energyCorrelation D H j k t : ℂ)) ∧
      coordinateHessianAtZero (energyCGF D (fun _ => beta0)) j k =
        -(∫ t in Set.Ioi (0 : ℝ), energyCorrelation D H j k t + energyCorrelation D H k j t) +
        (if j = k then evaluate (qdsGibbsDensity H beta0) (dissipation (D.generator j) H H) else 0)) ∧
    (∀ Theta : Mat d → Mat d,
      TimeReversible (qdsGibbsDensity H beta0) (reservoirGenerator D) Theta →
      (∀ j, Theta (energyFlux D H j) = energyFlux D H j) →
      ∀ t : ℝ, 0 ≤ t → ∀ j k,
        expect (qdsGibbsDensity H beta0) (qdsEvolution (reservoirGenerator D) t (energyFlux D H j) * energyFlux D H k) =
          expect (qdsGibbsDensity H beta0) (Theta (energyFlux D H k * qdsEvolution (reservoirGenerator D) t (energyFlux D H j))) ∧
        expect (qdsGibbsDensity H beta0) (Theta (energyFlux D H k * qdsEvolution (reservoirGenerator D) t (energyFlux D H j))) =
          expect (qdsGibbsDensity H beta0) (energyFlux D H k * qdsEvolution
            (weightedAdjoint (qdsGibbsDensity H beta0) (reservoirGenerator D)) t (energyFlux D H j)) ∧
        expect (qdsGibbsDensity H beta0) (energyFlux D H k * qdsEvolution
            (weightedAdjoint (qdsGibbsDensity H beta0) (reservoirGenerator D)) t (energyFlux D H j)) =
          expect (qdsGibbsDensity H beta0) (qdsEvolution (reservoirGenerator D) t (energyFlux D H k) * energyFlux D H j)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P34

end
