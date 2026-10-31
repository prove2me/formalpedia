-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P42_relativeEntanglement_le_formation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P42.relativeEntanglement_le_formation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:46:24.077305+00:00
-- url     : https://prove2.me/theorems/e0975b73-619d-4911-9059-229912bdca86
-- title:
--   Theorem 6: comparison with entanglement of creation
-- statement:
--   All local registers are nonzero and finite-dimensional. Density matrices are positive semidefinite with trace one. Entropies use natural logarithms, $0\ln0=0$, and Umegaki relative entropy $S(\sigma\Vert\rho)$ is $+\infty$ on failure of support inclusion. The relative entropy of entanglement is $E_R(\sigma)=\inf_{\rho\in\mathrm{Sep}}S(\sigma\Vert\rho)$, where separability is across the specified Alice:Bob cut.
--
--   Define the creation/formation roof by $E_c(\sigma)=\inf_{\sigma=\sum_i p_i|\psi_i\rangle\langle\psi_i|}\sum_i p_i S(\operatorname{Tr}_A|\psi_i\rangle\langle\psi_i|)$, over finite ensembles of unit vectors with nonnegative weights summing to one. Then
--
--   $$E_R(\sigma)\le E_c(\sigma).$$
--
--   This compares static functionals; it does not identify a one-copy roof with an asymptotic operational cost.
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, PDF p. 16, Theorem 6: comparison with entanglement of creation

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

/-- Theorem 6, PDF p.16, corrected by Eq.(6) and proof (40)–(41): E_R ≤ E_c.
The printed identification of E_c with min S is erroneous; creation is the pure-state roof. -/
theorem relativeEntanglement_le_formation {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (sigma : Matrix (I × J) (I × J) ℂ) (hsigma : IsDensityMatrix sigma) :
    relativeEntanglementNats sigma ≤ formationNats sigma := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P42

end
