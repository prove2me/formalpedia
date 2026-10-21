-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P30_vacuum_thermal_example
-- name    : QAlgorithms.Papers.Independent.Claimed50.P30.vacuum_thermal_example
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:23:16.569847+00:00
-- url     : https://prove2.me/theorems/697e922d-bea1-48af-8ffc-84e3bd9883a7
-- title:
--   Vacuum versus thermal state: all computed bounds and comparison
-- statement:
--   Let $\beta\ge1$ be finite. In one oscillator mode with vacuum covariance $I$, consider the actual thermal densities
--   $$
--   \rho_A=\sigma(1)=|0\rangle\langle0|,\qquad
--   \rho_B=\sigma(\beta),\qquad
--   \sigma(x)=\sum_{j\ge0}\frac{2}{x+1}\left(\frac{x-1}{x+1}\right)^j|j\rangle\langle j|.
--   $$
--   Both displacements vanish, the covariances are $I$ and $\beta I$, and their normal symplectic matrices are $I$. Define $\Phi_p^\pm(x)=(x+1)^p\pm(x-1)^p$ and $\Gamma_p(x)=[(x+1)^{2p}-(x-1)^{2p}]^{-1/2}$. For $p>0$ and $x\ge1$,
--   $$
--   \Phi_p^+(1)=\Phi_p^-(1)=[\Gamma_p(1)]^{-1}=2^p,\qquad
--   \Phi_p^+(x)+\Phi_p^-(x)=2(x+1)^p.
--   $$
--   In this one-mode case, the functions of (61),(73) are
--   $$
--   M_s=\frac{4}{\Phi_s^+(1)\Phi_{1-s}^-(\beta)+\Phi_{1-s}^+(\beta)\Phi_s^-(1)},\qquad
--   Y_s=2\Gamma_s(1)\Gamma_{1-s}(\beta).
--   $$
--   For $0<s<1$, they satisfy
--   $$
--   M_s=\left(\frac{2}{1+\beta}\right)^{1-s},\qquad
--   Y_{1-s}=\frac{2^s}{\sqrt{(\beta+1)^{2s}-(\beta-1)^{2s}}}.
--   $$
--   The limiting values are $M_s\to2/(1+\beta)$ as $s\to0^+$ and $Y_{1-s}\to1/\sqrt\beta$ as $s\to1^-$. For a single copy, with equal priors and interior infima in the definitions of $M^{(1)},Y^{(1)}$, this gives
--   $$
--   M^{(1)}=\frac1{1+\beta},\qquad Y^{(1)}=\frac1{2\sqrt\beta}.
--   $$
--   Here $P_{\mathrm{QC}}^{(1)}=\tfrac12\inf_{0<s<1}\operatorname{Tr}(\rho_A^s\rho_B^{1-s})$ is the equal-prior quantum Chernoff bound. Let $F=[\operatorname{Tr}\sqrt{\sqrt{\rho_A}\rho_B\sqrt{\rho_A}}]^2$ be the squared Uhlmann fidelity, and define $F_-=(1-\sqrt{1-F})/2$ and $F_+=\sqrt F/2$. Then
--   $$
--   F=\frac2{1+\beta},\qquad
--   F_-=\frac12-\frac12\sqrt{\frac{\beta-1}{\beta+1}},\qquad
--   F_+=\frac1{\sqrt{2(1+\beta)}},\qquad
--   P_{\mathrm{QC}}^{(1)}=\frac1{1+\beta}.
--   $$
--   Consequently,
--   $$
--   Y^{(1)}\le F_+,\qquad M^{(1)}=P_{\mathrm{QC}}^{(1)}.
--   $$
--   This worked example compares the two spectral upper bounds with the fidelity upper bound. At $\beta=1$ all upper bounds are $1/2$, so the comparison is non-strict.
--
--   **Formalization Note** The second expression in printed (85), labeled $Y_s$, equals $Y_{1-s}$ under the original definition (73). The explicit reparameterization above preserves the infimum and the numerical result (86); its limiting minimizer is $s=1$. No optimal Helstrom-error formula is asserted.
-- source:
--   Computable bounds for the discrimination of Gaussian states, arXiv:0806.1625v2, PDF p. 7, Section IV A, Eqs. (84)–(89)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P30

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal ComplexOrder Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Mathlib supplies this C-star functional calculus as a theorem, not a global instance.

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Claimed50.P30

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass IsPositive operatorTrace)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P04 (Covariance)

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- Section IV A, arXiv:0806.1625v2, PDF pp.6--7, (84)--(89).
In the second part of printed (85), Y_s uses s instead of 1-s relative to
(73). We explicitly write Y_(1-s); its infimum is unchanged. Printed/changed/why:
Y_s -> Y_(1-s), because substitution of alpha=1 into (73) gives the reverse
parameter. The limiting minimizer is s=1 in that reparameterized expression.
At beta=1 the states coincide and every upper bound is 1/2; comparison is <=.
Independent moderation of this source correction remains for the next stage. -/
theorem vacuum_thermal_example (W : FockWeylSystem 1) (beta : ℝ) (hbeta : 1 ≤ beta) :
    let alpha : Fin 1 → ℝ := fun _ => 1
    let spectrum : Fin 1 → ℝ := fun _ => beta
    let rhoA := thermalTensorDensity alpha
    let rhoB := thermalTensorDensity spectrum
    let F := operatorSquaredFidelity rhoA rhoB
    Summable (thermalTerm alpha) ∧ Summable (thermalTerm spectrum) ∧
    GaussianMoments W rhoA 0 (repeatedDiagonal alpha) ∧
    GaussianMoments W rhoB 0 (repeatedDiagonal spectrum) ∧
    rhoA = InnerProductSpace.rankOne ℂ
      (numberKet (fun _ : Fin 1 => 0)) (numberKet (fun _ : Fin 1 => 0)) ∧
    (∀ p : ℝ, 0 < p →
      phiPlus p 1 = Real.rpow 2 p ∧ phiMinus p 1 = Real.rpow 2 p ∧
      (spectralGamma p 1)⁻¹ = Real.rpow 2 p ∧
      ∀ x : ℝ, 1 ≤ x → phiPlus p x + phiMinus p x = 2 * Real.rpow (x + 1) p) ∧
    (∀ s : ℝ, 0 < s → s < 1 →
      minkowskiFunction alpha spectrum s = Real.rpow (2 / (1 + beta)) (1 - s) ∧
      youngFunction alpha spectrum (1 - s) =
        Real.rpow 2 s / Real.sqrt
          (Real.rpow (beta + 1) (2 * s) - Real.rpow (beta - 1) (2 * s))) ∧
    Tendsto (minkowskiFunction alpha spectrum)
      (nhdsWithin 0 (Set.Ioo (0 : ℝ) 1)) (𝓝 (2 / (1 + beta))) ∧
    Tendsto (fun s => youngFunction alpha spectrum (1 - s))
      (nhdsWithin 1 (Set.Ioo (0 : ℝ) 1)) (𝓝 (1 / Real.sqrt beta)) ∧
    minkowskiBound alpha spectrum 1 = ENNReal.ofReal ((1 + beta)⁻¹) ∧
    youngBound alpha spectrum 1 = ENNReal.ofReal (1 / (2 * Real.sqrt beta)) ∧
    F = 2 / (1 + beta) ∧
    fidelityLower F = 1 / 2 - Real.sqrt ((beta - 1) / (beta + 1)) / 2 ∧
    fidelityUpper F = 1 / Real.sqrt (2 * (1 + beta)) ∧
    quantumChernoff rhoA rhoB 1 = ENNReal.ofReal ((1 + beta)⁻¹) ∧
    youngBound alpha spectrum 1 ≤ ENNReal.ofReal (fidelityUpper F) ∧
    minkowskiBound alpha spectrum 1 = quantumChernoff rhoA rhoB 1 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P30

end
