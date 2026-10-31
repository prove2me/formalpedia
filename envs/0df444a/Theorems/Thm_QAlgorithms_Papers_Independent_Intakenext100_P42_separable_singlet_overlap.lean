-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P42_separable_singlet_overlap
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P42.separable_singlet_overlap
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:53:18.521581+00:00
-- url     : https://prove2.me/theorems/ac368ffa-f35a-4304-a161-f0c557e7f6eb
-- title:
--   Unnumbered supporting fact: separable singlet overlap
-- statement:
--   All local registers are nonzero and finite-dimensional. Density matrices are positive semidefinite with trace one. Entropies use natural logarithms, $0\ln0=0$, and Umegaki relative entropy $S(\sigma\Vert\rho)$ is $+\infty$ on failure of support inclusion. The relative entropy of entanglement is $E_R(\sigma)=\inf_{\rho\in\mathrm{Sep}}S(\sigma\Vert\rho)$, where separability is across the specified Alice:Bob cut.
--
--   For $m\ge0$, let $\rho$ be any normalized state separable across the full $A^m:B^m$ cut, and write $|\Phi_m\rangle=2^{-m/2}\sum_{x\in\{0,1\}^m}|x\rangle|x\rangle$. Then
--
--   $$\langle\Phi_m|\rho|\Phi_m\rangle\le2^{-m}.$$
--
--   This is a joint-overlap bound, without an independence assumption on marginal pairs. At zero pairs it is the scalar unit bound.
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, PDF p. 31, Unnumbered supporting fact: separable singlet overlap

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

/-- PDF pp.31,38: JOINT overlap of m Bell pairs with a state separable across the
full Alice:Bob cut, rather than a product of marginal overlap estimates. -/
theorem separable_singlet_overlap (m : ℕ)
    (rho : Matrix (Qubits m × Qubits m) (Qubits m × Qubits m) ℂ)
    (hrho : IsSeparableDensity rho) :
    effectProb (pureDensity (maxEntangled m)) rho ≤ 1 / (2 : ℝ)^m := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P42

end
