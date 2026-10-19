-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_dirichletMonomialMoments
-- name    : QAlgorithms.Papers.Independent.Information100.P37.dirichletMonomialMoments
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:20:47.145111+00:00
-- url     : https://prove2.me/theorems/33c2a64e-993e-4b95-8def-6dc5f55b4e89
-- title:
--   Lemma 20, Dirichlet monomial moments
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   For nonnegative integer exponents $m_1,\ldots,m_d$, let $m=\sum_im_i$. Then
--   $$\mathbb E_{\nu_d}\prod_{i=1}^dp_i^{m_i}=\frac{(d-1)!\prod_im_i!}{(d+m-1)!}.$$
--   The fourth-order specializations are $\mathbb E p_i^4=24/D_d$, $\mathbb E p_i^3p_j=6/D_d$, $\mathbb E p_i^2p_j^2=4/D_d$, $\mathbb E p_i^2p_jp_k=2/D_d$, and $\mathbb E p_ip_jp_kp_l=1/D_d$, with all displayed distinct index letters pairwise distinct in each applicable formula.
--
--   These monomial moments are valid at $d=1$ and supply the fourth-order contraction coefficients.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 13, Lemma 20, Dirichlet monomial moments

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF p.13, Lemma 20, (A3),(A5): monomial moments and all fourth-order multiplicities. -/
theorem dirichletMonomialMoments (d : ℕ) (hd : 1 ≤ d) :
    (∀ a : Fin d → ℕ, (∫ p, ∏ i, p i ^ a i ∂simplexLaw (Fin d)) =
      ((Nat.factorial (d - 1) : ℝ) * ∏ i, (Nat.factorial (a i) : ℝ)) /
        (Nat.factorial (d + (∑ i, a i) - 1) : ℝ)) ∧
    (∀ i : Fin d, (∫ p, p i ^ 4 ∂simplexLaw (Fin d)) = 24 / fourthDenominator d) ∧
    (∀ i j : Fin d, i ≠ j →
      (∫ p, p i ^ 3 * p j ∂simplexLaw (Fin d)) = 6 / fourthDenominator d) ∧
    (∀ i j : Fin d, i ≠ j →
      (∫ p, p i ^ 2 * p j ^ 2 ∂simplexLaw (Fin d)) = 4 / fourthDenominator d) ∧
    (∀ i j k : Fin d, i ≠ j → i ≠ k → j ≠ k →
      (∫ p, p i ^ 2 * p j * p k ∂simplexLaw (Fin d)) = 2 / fourthDenominator d) ∧
    (∀ i j k l : Fin d, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      (∫ p, p i * p j * p k * p l ∂simplexLaw (Fin d)) = 1 / fourthDenominator d) := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
