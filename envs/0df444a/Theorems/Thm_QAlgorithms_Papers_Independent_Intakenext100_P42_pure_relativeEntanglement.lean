-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P42_pure_relativeEntanglement
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P42.pure_relativeEntanglement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:38:59.836204+00:00
-- url     : https://prove2.me/theorems/f999636a-fe0d-4f48-a78b-081b5750cbbc
-- title:
--   Theorem 3: pure-state relative entropy of entanglement
-- statement:
--   All local registers are nonzero and finite-dimensional. Density matrices are positive semidefinite with trace one. Entropies use natural logarithms, $0\ln0=0$, and Umegaki relative entropy $S(\sigma\Vert\rho)$ is $+\infty$ on failure of support inclusion. The relative entropy of entanglement is $E_R(\sigma)=\inf_{\rho\in\mathrm{Sep}}S(\sigma\Vert\rho)$, where separability is across the specified Alice:Bob cut.
--
--   Let $\{u_k\}$ and $\{v_k\}$ be finite orthonormal local families, and let $p_k\ge0$ sum to one. Put $|\psi\rangle=\sum_k\sqrt{p_k}|u_kv_k\rangle$, $\sigma=|\psi\rangle\langle\psi|$, and $\sigma_B=\operatorname{Tr}_A\sigma$. Then
--
--   $$E_R(\sigma)=-\sum_kp_k\ln p_k=-\operatorname{Tr}(\sigma_B\ln\sigma_B).$$
--
--   This identifies pure-state relative entropy of entanglement with reduced entropy, including zero Schmidt weights and unequal local dimensions.
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, PDF p. 12, Theorem 3: pure-state relative entropy of entanglement

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

/-- Theorem 3, PDF pp.12–14: arbitrary finite-dimensional pure-state relative entropy
of entanglement equals its Schmidt entropy and its reduced von Neumann entropy. -/
theorem pure_relativeEntanglement {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J] (s : FiniteSchmidtExpansion I J K) :
    relativeEntanglementNats (pureDensity (finiteSchmidtVector s)) = (finiteSchmidtEntropyNats s : EReal) ∧
    relativeEntanglementNats (pureDensity (finiteSchmidtVector s)) =
      (entropy (traceLeft (pureDensity (finiteSchmidtVector s))) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P42

end
