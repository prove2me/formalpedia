-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P41_mutualRenyi_firstOrder
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P41.mutualRenyi_firstOrder
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:54:52.507147+00:00
-- url     : https://prove2.me/theorems/3d4aa5cb-c0d3-4c7d-886d-845c640fedd9
-- title:
--   Linear mutual Renyi response and quadratic mutual information at a product state
-- statement:
--   Let $A$ and $B$ be arbitrary finite regulated Hilbert factors, let $\widehat\rho_A$ and $\widehat\rho_B$ be positive trace-one density matrices, and set $\rho_0=\widehat\rho_A\otimes\widehat\rho_B$. Let $\rho(t)=\rho_0+t\rho_1$ be normalized and positive with unchanged occupied support for sufficiently small real $t$ of either sign, where $\rho_1$ is Hermitian, has trace zero, and has image in the occupied support of $\rho_0$. Define the actual marginals by $\rho_A(t)=\operatorname{Tr}_B\rho(t)$ and $\rho_B(t)=\operatorname{Tr}_A\rho(t)$, and put $I_\alpha(t)=S_\alpha(\rho_A(t))+S_\alpha(\rho_B(t))-S_\alpha(\rho(t))$. For fixed $\alpha>0$, $\alpha\ne1$, define
--
--   $$
--   D_X=\frac{\widehat\rho_X^{\alpha-1}}{\operatorname{Tr}\widehat\rho_X^\alpha}-\mathbf1_X\quad(X=A,B).
--   $$
--
--   Then
--
--   $$
--   I_\alpha(t)=t\frac{\alpha}{\alpha-1}\operatorname{Tr}\!\left[\rho_1(D_A\otimes D_B)\right]+O(t^2),
--   \qquad I_1(t)=O(t^2).
--   $$
--
--   All logarithms are natural, powers are on occupied support, and the error estimates are two-sided at zero for fixed data. This distinguishes the possible linear Renyi response from the quadratic onset of mutual information. No universal nonzero quadratic coefficient is asserted.
--
--   **Formalization Note** Both marginals are computed using the frozen partial-trace definitions at each parameter. The theorem concerns the regulated finite-rank interpretation, not an unqualified infinite-dimensional extension.
-- source:
--   Entanglement Renyi entropies in holographic theories, arXiv:1006.0047v3, PDF p. 8, §2.2, (2.11)–(2.13)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P41

namespace QAlgorithms.Papers.Independent.Intakethird100.P41

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open scoped Topology

/-- PDF pp.7-8, (2.11)-(2.13): MRI has the displayed linear response about a product
state and MI has a quadratic remainder. Marginals are computed by partial trace at each
parameter, not held fixed. This states the regulated finite-rank interpretation; it makes
no assertion that the quadratic coefficient is nonzero for every perturbation. -/
theorem mutualRenyi_firstOrder {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (rhoA : Matrix A A ℂ) (rhoB : Matrix B B ℂ)
    (hA : QAlgorithms.IsDensityMatrix rhoA) (hB : QAlgorithms.IsDensityMatrix rhoB)
    (rho1 : Matrix (A × B) (A × B) ℂ)
    (hpert : IsSupportPreservingPerturbation (Matrix.kronecker rhoA rhoB) rho1)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    Asymptotics.IsBigO (𝓝 (0 : ℝ))
      (fun t : ℝ => mutualRenyiNats a
        (densityPerturbation (Matrix.kronecker rhoA rhoB) rho1 t) -
        t * (a / (a - 1) *
          (rho1 * Matrix.kronecker (centeredPower a rhoA)
            (centeredPower a rhoB)).trace.re))
      (fun t : ℝ => t ^ 2) ∧
    Asymptotics.IsBigO (𝓝 (0 : ℝ))
      (fun t : ℝ => mutualRenyiNats 1
        (densityPerturbation (Matrix.kronecker rhoA rhoB) rho1 t))
      (fun t : ℝ => t ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P41
