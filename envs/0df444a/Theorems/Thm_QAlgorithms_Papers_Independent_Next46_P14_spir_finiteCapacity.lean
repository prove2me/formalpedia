-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P14_spir_finiteCapacity
-- name    : QAlgorithms.Papers.Independent.Next46.P14.spir_finiteCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:09:51.561983+00:00
-- url     : https://prove2.me/theorems/b4c78738-d9cb-4d92-bd30-d2ccd3a59d17
-- title:
--   Finite-length zero-error SPIR capacity
-- statement:
--   Let K and N be positive integers. Consider K independent messages replicated at N noncommunicating, noncolluding servers over the prime field $\mathbb F_p$. Message k has $\ell_k L$ independent uniform symbols, where all multipliers and L are positive integers. The user seed F, uniform requested index, messages, and shared server seed S are mutually independent. Queries depend only on F and the requested index; each server answers using only its received query, all messages, and S. User privacy compares the full server views $(Q_n,A_n,W_{1:K},S)$; database privacy requires the joint undesired-message vector to be independent of the full user view $(Q_{1:N},A_{1:N},F)$. Download D is the maximum total number of field symbols, with query-specified answer lengths; upload is not charged. The exact rate for request k is $R_k=\ell_k L/D$. Entropies use p-ary units. Assume $K,N\geq2$, $\ell_k=1$, a fixed $L\geq1$, and $\rho\geq0$. Impose the finite-length convention from p.12 that $H_p(S)$ is an integer, with available budget $H_p(S)\leq\rho L$. Optimize over protocols having exact correctness and both exact privacy properties. Then
--
--   $$C_{o,L}=\begin{cases}\dfrac{L}{\lceil L/(1-1/N)\rceil},&\rho\geq\lceil L/(N-1)\rceil/L,\\0,&\text{otherwise}.\end{cases}$$
--
--   This records the finite-block ceiling penalty and the separate rounded randomness threshold.
-- source:
--   The Capacity of Symmetric Private Information Retrieval, arXiv:1606.08828v2, PDF p. 7, Theorem 3, (16)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P14

noncomputable section

open scoped BigOperators ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P14

/-- Theorem 3, PDF p.7, (16), and PDF p.12: fixed-L zero-error spirCapacity.
The direct denominator 1−1/N avoids the circular zero branch of C_SPIR.
Only spirFiniteCapacity imposes integral common-randomness spirEntropy. -/
theorem spir_finiteCapacity (m : SpirParameters) (hK : 2 ≤ m.K) (hN : 2 ≤ m.N)
    (hequal : ∀ k, m.ell k = 1) (L : ℕ) (hL : 0 < L) (rho : ℝ) (hrho : 0 ≤ rho) :
    spirFiniteCapacity m L rho =
      if (⌈(L : ℝ) / ((m.N : ℝ) - 1)⌉₊ : ℝ) / (L : ℝ) ≤ rho then
        ENNReal.ofReal ((L : ℝ) / (⌈(L : ℝ) / (1 - 1 / (m.N : ℝ))⌉₊ : ℝ))
      else 0 := by sorry

end QAlgorithms.Papers.Independent.Next46.P14

end
