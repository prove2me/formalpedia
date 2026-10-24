-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P14_logarithmicNegativity_counterexample
-- name    : QAlgorithms.Papers.Independent.Support50.P14.logarithmicNegativity_counterexample
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:32:55.388575+00:00
-- url     : https://prove2.me/theorems/dd2289c4-7d5f-486d-b8de-bf873d537a01
-- title:
--   Unnumbered explicit failure for logarithmic negativity
-- statement:
--   On two complete oscillator modes, set $|\phi\rangle=(\sqrt{15}/4)|00\rangle+(1/4)|11\rangle$, and let $\rho=|\phi\rangle\langle\phi|$. This is a normalized density with zero first moments, diagonal covariance blocks $(9/8)I$, and cross block $\operatorname{diag}(\sqrt{15}/8,-\sqrt{15}/8)$. A Gaussian density $\rho_G$ with these same moments exists. Both partial transposes are trace class with finite trace norm at least one. For $E_N(\sigma)=\log_2\|\sigma^{T_A}\|_1$,
--
--   $$E_N(\rho)=\log_2(1+\sqrt{15}/8)<-\log_2((9-\sqrt{15})/8)=E_N(\rho_G).$$
--
--   This exact strict inequality is the counterexample witnessed by the source's rounded decimals. It shows that covariance-based Gaussian substitution can overestimate logarithmic negativity.
-- source:
--   Extremality of Gaussian quantum states, arXiv:quant-ph/0509154v1, PDF p. 3, Unnumbered explicit failure for logarithmic negativity

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14

noncomputable section

open Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support50.P14

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClass traceSize)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (unitaryCoeff conjugateKernel boundedUnitaryConjugation)

open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

/-- Explicit failure for logarithmic negativity, PDF p.3, application (iv).
The printed approximate decimals witness the exact strict inequality below.
Partial-transpose nuclearity and finite trace norms are conclusions, as are the
moments of the constructed rank-one density and of its Gaussian counterpart. -/
theorem logarithmicNegativity_counterexample :
    IsDensity counterexampleState ∧
    CompleteMoments counterexampleState 0 negativityExampleCovariance ∧
    ∃ rhoG : State (Occupation (Fin 2)),
      GaussianAt rhoG.coefficients 0 negativityExampleCovariance ∧
      IsTraceClass (transposeFirst counterexampleState) ∧
      IsTraceClass (transposeFirst rhoG.coefficients) ∧
      1 ≤ traceSize (transposeFirst counterexampleState) ∧
      traceSize (transposeFirst counterexampleState) < ⊤ ∧
      1 ≤ traceSize (transposeFirst rhoG.coefficients) ∧
      traceSize (transposeFirst rhoG.coefficients) < ⊤ ∧
      logarithmicNegativity counterexampleState = Real.logb 2 (1 + Real.sqrt 15 / 8) ∧
      logarithmicNegativity rhoG.coefficients = -Real.logb 2 ((9 - Real.sqrt 15) / 8) ∧
      logarithmicNegativity counterexampleState < logarithmicNegativity rhoG.coefficients := by sorry

end QAlgorithms.Papers.Independent.Support50.P14

end
