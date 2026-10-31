-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P42_pure_minimizer
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P42.pure_minimizer
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:44:25.393976+00:00
-- url     : https://prove2.me/theorems/5d5add7b-20a2-4d64-ac3f-59f00f1472df
-- title:
--   Proposition: explicit Schmidt-diagonal minimizer
-- statement:
--   All local registers are nonzero and finite-dimensional. Density matrices are positive semidefinite with trace one. Entropies use natural logarithms, $0\ln0=0$, and Umegaki relative entropy $S(\sigma\Vert\rho)$ is $+\infty$ on failure of support inclusion. The relative entropy of entanglement is $E_R(\sigma)=\inf_{\rho\in\mathrm{Sep}}S(\sigma\Vert\rho)$, where separability is across the specified Alice:Bob cut.
--
--   For an orthonormal Schmidt expansion $|\psi\rangle=\sum_k\sqrt{p_k}|u_kv_k\rangle$, with $p_k\ge0$ summing to one, put $\sigma=|\psi\rangle\langle\psi|$ and $\rho_*=\sum_kp_k|u_kv_k\rangle\langle u_kv_k|$. The constructed $\rho_*$ is separable, and
--
--   $$S(\sigma\Vert\rho_*)=-\sum_kp_k\ln p_k\le S(\sigma\Vert\rho)\quad(\rho\in\mathrm{Sep}).$$
--
--   This is the explicit minimizing-state certificate supporting Theorem 3.
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, PDF p. 14, Proposition: explicit Schmidt-diagonal minimizer

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

/-- Proposition and its proof, PDF pp.13–14: explicit Schmidt-diagonal minimizer
certificate, supporting the entropy equality of Theorem 3. -/
theorem pure_minimizer {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J] (s : FiniteSchmidtExpansion I J K) :
    IsMinimizer (pureDensity (finiteSchmidtVector s)) (schmidtDiagonal s) ∧
      relativeEntropy (pureDensity (finiteSchmidtVector s)) (schmidtDiagonal s) =
        (finiteSchmidtEntropyNats s : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P42

end
