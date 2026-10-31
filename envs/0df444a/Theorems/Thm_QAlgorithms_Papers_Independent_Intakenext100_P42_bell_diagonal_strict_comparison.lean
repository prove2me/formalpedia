-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P42_bell_diagonal_strict_comparison
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P42.bell_diagonal_strict_comparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:54:29.124917+00:00
-- url     : https://prove2.me/theorems/4a13f790-a55b-4f9e-80f5-d183839ca500
-- title:
--   Unnumbered: strict Bell-diagonal creation comparison and Fig.2
-- statement:
--   All local registers are nonzero and finite-dimensional. Density matrices are positive semidefinite with trace one. Entropies use natural logarithms, $0\ln0=0$, and Umegaki relative entropy $S(\sigma\Vert\rho)$ is $+\infty$ on failure of support inclusion. The relative entropy of entanglement is $E_R(\sigma)=\inf_{\rho\in\mathrm{Sep}}S(\sigma\Vert\rho)$, where separability is across the specified Alice:Bob cut.
--
--   Let $p_i\ge0$ sum to one and let $\sigma=\sum_{i=1}^4p_i|\mathrm{Bell}_i\rangle\langle\mathrm{Bell}_i|$. Then
--
--   $$\tfrac12<\max_i p_i<1\quad\Longrightarrow\quad E_R(\sigma)<E_c(\sigma).$$
--
--   When every $p_i\le1/2$, both functionals vanish; when some $p_i=1$, both equal $\ln2$. This retains exactly the equality exceptions in the p.33 strict static comparison.
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, PDF p. 33, Unnumbered: strict Bell-diagonal creation comparison and Fig.2

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

/-- PDF pp.16,33 and Fig.2 pp.42,44: strict creation comparison for mixed entangled
Bell-diagonal states; equality on the separable regime and pure Bell endpoints. -/
theorem bell_diagonal_strict_comparison (p : Fin 4 → ℝ)
    (hp : ∀ i, 0 ≤ p i) (htotal : ∑ i, p i = 1) :
    ((∃ i, 1/2 < p i ∧ p i < 1) →
      relativeEntanglementNats (bellDiagonal p) < formationNats (bellDiagonal p)) ∧
    ((∀ i, p i ≤ 1/2) →
      relativeEntanglementNats (bellDiagonal p) = 0 ∧ formationNats (bellDiagonal p) = 0) ∧
    ((∃ i, p i = 1) →
      relativeEntanglementNats (bellDiagonal p) = (Real.log 2 : EReal) ∧
      formationNats (bellDiagonal p) = (Real.log 2 : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P42

end
