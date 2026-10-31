-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P42_example_three
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P42.example_three
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:51:16.517188+00:00
-- url     : https://prove2.me/theorems/3764b3a3-8fd3-46ad-9ef1-ee366558e48e
-- title:
--   Example 3: maximally correlated two-qubit family
-- statement:
--   All local registers are nonzero and finite-dimensional. Density matrices are positive semidefinite with trace one. Entropies use natural logarithms, $0\ln0=0$, and Umegaki relative entropy $S(\sigma\Vert\rho)$ is $+\infty$ on failure of support inclusion. The relative entropy of entanglement is $E_R(\sigma)=\inf_{\rho\in\mathrm{Sep}}S(\sigma\Vert\rho)$, where separability is across the specified Alice:Bob cut.
--
--   Let $A\in[0,1]$ and $B\in\mathbb C$ satisfy $|B|^2\le A(1-A)$. Put $\sigma_3=A|00\rangle\langle00|+B|00\rangle\langle11|+\overline B|11\rangle\langle00|+(1-A)|11\rangle\langle11|$ and $\rho_3=A|00\rangle\langle00|+(1-A)|11\rangle\langle11|$. Then $\rho_3$ is a separable minimizer and, for $e_\pm=(1\pm\sqrt{(2A-1)^2+4|B|^2})/2$,
--
--   $$E_R(\sigma_3)=e_+\ln e_++e_-\ln e_--A\ln A-(1-A)\ln(1-A).$$
--
--   Complex phases, zero coherence and pure endpoints are included.
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, PDF p. 24, Example 3: maximally correlated two-qubit family

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

/-- Example 3, PDF p.24, Eqs.(63)–(66): the corrected discriminant has +4|B|^2.
Complex phases, zero coherence, and pure endpoints are all retained. -/
theorem example_three (a : ℝ) (b : ℂ) (ha : a ∈ Set.Icc 0 1)
    (hb : Complex.normSq b ≤ a*(1-a)) :
    IsMinimizer (correlated a b) (correlatedMinimum a) ∧
    relativeEntanglementNats (correlated a b) =
      ((correlatedEigenvalue a b true * Real.log (correlatedEigenvalue a b true) +
        correlatedEigenvalue a b false * Real.log (correlatedEigenvalue a b false) -
        a*Real.log a - (1-a)*Real.log (1-a) : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P42

end
