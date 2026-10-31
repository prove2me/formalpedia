-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P42_example_two
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P42.example_two
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:50:34.252039+00:00
-- url     : https://prove2.me/theorems/ef16a6d6-92e0-4285-9cc3-11535d76a154
-- title:
--   Example 2: Bell plus |00><00|
-- statement:
--   All local registers are nonzero and finite-dimensional. Density matrices are positive semidefinite with trace one. Entropies use natural logarithms, $0\ln0=0$, and Umegaki relative entropy $S(\sigma\Vert\rho)$ is $+\infty$ on failure of support inclusion. The relative entropy of entanglement is $E_R(\sigma)=\inf_{\rho\in\mathrm{Sep}}S(\sigma\Vert\rho)$, where separability is across the specified Alice:Bob cut.
--
--   For $\lambda\in[0,1]$, put $\sigma_2=\lambda|\Phi^+\rangle\langle\Phi^+|+(1-\lambda)|00\rangle\langle00|$ and $\rho_2=(1-\lambda/2)|00\rangle\langle00|+(\lambda/2)|11\rangle\langle11|$. The state $\rho_2$ is a separable minimizer. With $s_\pm=(1\pm\sqrt{1-2\lambda(1-\lambda)})/2$,
--
--   $$E_R(\sigma_2)=s_+\ln s_++s_-\ln s_--(1-\lambda/2)\ln(1-\lambda/2)-(\lambda/2)\ln(\lambda/2).$$
--
--   The formula includes the product and Bell endpoints.
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, PDF p. 23, Example 2: Bell plus |00><00|

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P42

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P42

open QAlgorithms QAlgorithms.Entanglement

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P04 (copies)

open QAlgorithms.Papers.Independent.Bridge50.P49 (groupedProduct)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Example 2, PDF pp.23–24, corrected Eqs.(61)–(62).
The final diagonal entropy term is (t/2)ln(t/2), and the radicand is 1-2t(1-t),
as forced by Eq.(59)'s determinant; the printed radicand fails at t=1. -/
theorem example_two (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    let sp := (1+Real.sqrt (1-2*t*(1-t)))/2
    let sm := (1-Real.sqrt (1-2*t*(1-t)))/2
    IsMinimizer (exampleTwoInput t) (correlatedMinimum (1-t/2)) ∧
    relativeEntanglementNats (exampleTwoInput t) =
      ((sp*Real.log sp + sm*Real.log sm - (1-t/2)*Real.log (1-t/2) -
        (t/2)*Real.log (t/2) : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P42

end
