-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P42_optimized_werner_lower_bound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P42.optimized_werner_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:51:52.775288+00:00
-- url     : https://prove2.me/theorems/54513a2e-1e7d-4d4d-a036-27e675b13c18
-- title:
--   Unnumbered Eq.(73): optimized Werner lower bound
-- statement:
--   All local registers are nonzero and finite-dimensional. Density matrices are positive semidefinite with trace one. Entropies use natural logarithms, $0\ln0=0$, and Umegaki relative entropy $S(\sigma\Vert\rho)$ is $+\infty$ on failure of support inclusion. The relative entropy of entanglement is $E_R(\sigma)=\inf_{\rho\in\mathrm{Sep}}S(\sigma\Vert\rho)$, where separability is across the specified Alice:Bob cut.
--
--   For any two-qubit density matrix $\sigma$, let $F$ be its maximum overlap with a maximally entangled unit vector. The maximum is attained by a local-unitary image of $\Phi^+$. Let $W_F=F|\Psi^-\rangle\langle\Psi^-|+\frac{1-F}{3}(I-|\Psi^-\rangle\langle\Psi^-|)$. Then
--
--   $$E_R(\sigma)\ge E_R(W_F)=\begin{cases}0,&F\le\tfrac12,\\F\ln F+(1-F)\ln(1-F)+\ln2,&F>\tfrac12.\end{cases}$$
--
--   This is the optimized Werner lower bound for every input density matrix.
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, PDF p. 25, Unnumbered Eq.(73): optimized Werner lower bound

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

/-- PDF p.25, corrected Eq.(73): attained optimized Werner lower bound for EVERY input.
For F≤1/2 the Werner value is zero; the printed positive expression fails on I/4. -/
theorem optimized_werner_lower_bound (sigma : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (hsigma : IsDensityMatrix sigma) :
    let f := twoQubitMaxEntangledFraction sigma
    (∃ U V : Matrix.unitaryGroup Bool ℂ,
      effectProb (pureDensity (localBell U V)) sigma = f) ∧
    relativeEntanglementNats (singletWernerState f) = (wernerValue f : EReal) ∧
    relativeEntanglementNats (singletWernerState f) ≤ relativeEntanglementNats sigma := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P42

end
