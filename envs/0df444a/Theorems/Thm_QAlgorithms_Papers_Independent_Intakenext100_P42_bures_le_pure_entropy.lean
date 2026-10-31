-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P42_bures_le_pure_entropy
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P42.bures_le_pure_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:47:06.894221+00:00
-- url     : https://prove2.me/theorems/b205f7f4-84c1-4510-98c1-eade5ce2e98e
-- title:
--   Corollary after Theorem 7: comparison with reduced entropy
-- statement:
--   All local registers are nonzero and finite-dimensional. Density matrices are positive semidefinite with trace one. Entropies use natural logarithms, $0\ln0=0$, and Umegaki relative entropy $S(\sigma\Vert\rho)$ is $+\infty$ on failure of support inclusion. The relative entropy of entanglement is $E_R(\sigma)=\inf_{\rho\in\mathrm{Sep}}S(\sigma\Vert\rho)$, where separability is across the specified Alice:Bob cut.
--
--   Let $|\psi\rangle$ be any unit vector on two qubits, put $\sigma=|\psi\rangle\langle\psi|$ and $\sigma_B=\operatorname{Tr}_A\sigma$, and define $E_B(\sigma)=\inf_{\rho\in\mathrm{Sep}}[2-2\operatorname{Tr}\sqrt{\sqrt\sigma\rho\sqrt\sigma}]$. Then
--
--   $$E_B(\sigma)\le-\operatorname{Tr}(\sigma_B\ln\sigma_B).$$
--
--   The statement uses the source’s actual root-fidelity generator, independently of its erroneous Theorem 7 formula.
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, PDF p. 18, Corollary after Theorem 7: comparison with reduced entropy

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

/-- Corollary, PDF p.18, Eq.(45): the actual Bures-generated measure is bounded by
pure-state reduced entropy, in the two-qubit setting. The false intermediate (46) is not used. -/
theorem bures_le_pure_entropy (psi : EuclideanSpace ℂ (Bool × Bool)) (hpsi : ‖psi‖=1) :
    buresEntanglement (pureDensity psi) ≤ (entropy (traceLeft (pureDensity psi)) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P42

end
