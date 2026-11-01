-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P46_displacement_nonDecrease
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P46.displacement_nonDecrease
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:02:54.862673+00:00
-- url     : https://prove2.me/theorems/ee284bbe-4796-42eb-a978-7b74d18b6cb2
-- title:
--   §3, Eqs. (27),(28): displacement does not lower GRE
-- statement:
--   Let $\rho$ and $\sigma$ be centered Gaussian density operators on the same positive finite number of modes, represented by any two registers (either may be empty), and suppose $\sigma$ has a finite positive exponential matrix $M$. For real grouped phase vector $z$, let $\sigma_z=W(z)\sigma W(z)^*$, where $W(z)=\exp(iF^Tz)$. Its mean is $-\Delta z$ and its covariance equals that of $\sigma$. Then
--   $$D(\rho\Vert\sigma_z)=D(\rho\Vert\sigma)+\tfrac12(\Delta z)^TM(\Delta z)\ge D(\rho\Vert\sigma).$$
--   A common displacement first centers a noncentered input. The correction is positive, not an assertion that all displaced competitors have equal divergence. The displaced density is constructed by the bounded Weyl kernel on the completed oscillator space; its existence, Gaussian characteristic function, and preservation of separability are conclusions.
-- source:
--   Gaussian relative entropy of entanglement, arXiv:quant-ph/0402109v3, PDF p. 6, §3, Eqs. (27),(28): displacement does not lower GRE

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P46

open scoped BigOperators ENNReal ComplexOrder Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsSeparable)

open QAlgorithms.Papers.Independent.Dependency50.P13
  (finiteRelativeEntropy compression entropyWeight)

open QAlgorithms.Papers.Independent.Claimed50.P47
  (Occupation bipartiteCharacteristic bipartiteWeyl gaussianStateCharacteristic)

-- These accepted definitions have the same completed Hilbert-space meaning.

open QAlgorithms.Papers.Independent.Next46.P13 (coordinateBasis)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Claimed50.P41 (IsDiagonal)

/-- Chen, PDF p.6, (27)–(28): the constructed Weyl displacement is an actual
Gaussian density, preserves separability, and has the positive quadratic cost.
A common local displacement first centers nonzero input means. A single mode
is included by allowing one empty register, with a nonempty total mode set. -/
theorem displacement_nonDecrease {A B : Type} [Fintype A] [Fintype B]
    [Nonempty (A ⊕ B)]
    (rho sigma : State (Occupation A × Occupation B))
    (alpha beta M : ModeMatrix (A ⊕ B)) (z : GroupedPhase (A ⊕ B) → ℝ)
    (hrho : HasGaussian rho 0 alpha) (hsigma : HasGaussian sigma 0 beta)
    (hfinite : CMEM beta M) :
    ∃ sigmaz : State (Occupation A × Occupation B),
      sigmaz.coefficients = weylDisplacedDensity sigma z ∧
      HasGaussian sigmaz (-(groupedCCR (A ⊕ B)).mulVec z) beta ∧
      (IsSeparable sigmaz.coefficients ↔ IsSeparable sigma.coefficients) ∧
      0 ≤ displacementPenalty M z ∧
      operatorRelativeEntropy rho sigmaz = operatorRelativeEntropy rho sigma + ENNReal.ofReal (displacementPenalty M z) ∧
      operatorRelativeEntropy rho sigma ≤ operatorRelativeEntropy rho sigmaz := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P46

end
