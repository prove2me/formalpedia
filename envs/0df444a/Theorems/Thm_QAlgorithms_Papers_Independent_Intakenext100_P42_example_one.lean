-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P42_example_one
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P42.example_one
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:49:48.419713+00:00
-- url     : https://prove2.me/theorems/458c9f1e-6068-4a2e-aecd-27c2cad506d7
-- title:
--   Example 1: Bell plus orthogonal product
-- statement:
--   All local registers are nonzero and finite-dimensional. Density matrices are positive semidefinite with trace one. Entropies use natural logarithms, $0\ln0=0$, and Umegaki relative entropy $S(\sigma\Vert\rho)$ is $+\infty$ on failure of support inclusion. The relative entropy of entanglement is $E_R(\sigma)=\inf_{\rho\in\mathrm{Sep}}S(\sigma\Vert\rho)$, where separability is across the specified Alice:Bob cut.
--
--   For $\lambda\in[0,1]$, let $|\Phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2$ and $\sigma_1=\lambda|\Phi^+\rangle\langle\Phi^+|+(1-\lambda)|01\rangle\langle01|$. Put $c=\lambda(1-\lambda/2)/2$ and
--
--   $$\rho_1=c(|00\rangle\langle00|+|00\rangle\langle11|+|11\rangle\langle00|+|11\rangle\langle11|)+(1-\lambda/2)^2|01\rangle\langle01|+\frac{\lambda^2}{4}|10\rangle\langle10|.$$
--
--   Then $\rho_1$ is a separable minimizer, and
--
--   $$E_R(\sigma_1)=(\lambda-2)\ln(1-\lambda/2)+(1-\lambda)\ln(1-\lambda).$$
--
--   The endpoints give zero and $\ln2$; no uniqueness is asserted.
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, PDF p. 23, Example 1: Bell plus orthogonal product

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

/-- Example 1, PDF p.23, Eqs.(54)–(56): includes the constructed optimizer and both endpoints. -/
theorem example_one (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    IsMinimizer (exampleOneInput t) (exampleOneMinimum t) ∧
    relativeEntanglementNats (exampleOneInput t) =
      (((t-2)*Real.log (1-t/2) + (1-t)*Real.log (1-t) : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P42

end
