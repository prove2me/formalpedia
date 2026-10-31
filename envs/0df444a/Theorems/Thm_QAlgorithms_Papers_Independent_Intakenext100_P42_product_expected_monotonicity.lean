-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P42_product_expected_monotonicity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P42.product_expected_monotonicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:42:54.055187+00:00
-- url     : https://prove2.me/theorems/4f8d8452-e5e7-4380-b73a-48175b41dd09
-- title:
--   Unnumbered E3*: product input expected monotonicity
-- statement:
--   All local registers are nonzero and finite-dimensional. Density matrices are positive semidefinite with trace one. Entropies use natural logarithms, $0\ln0=0$, and Umegaki relative entropy $S(\sigma\Vert\rho)$ is $+\infty$ on failure of support inclusion. The relative entropy of entanglement is $E_R(\sigma)=\inf_{\rho\in\mathrm{Sep}}S(\sigma\Vert\rho)$, where separability is across the specified Alice:Bob cut.
--
--   Let $\sigma_1,\ldots,\sigma_n$ be bipartite density matrices, possibly on different local dimensions, and put $\Sigma=\bigotimes_j\sigma_j$, grouping all Alice factors against all Bob factors. For every complete product-Kraus family $V_i=A_i\otimes B_i$ across that cut, let $p_i=\operatorname{Tr}(V_i\Sigma V_i^\dagger)$. Then
--
--   $$\sum_{i:p_i>0}p_i E_R\!\left(\frac{V_i\Sigma V_i^\dagger}{p_i}\right)\le E_R(\Sigma).$$
--
--   The input remains the entanglement of the whole product; no additivity is assumed.
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, PDF p. 11, Unnumbered E3*: product input expected monotonicity

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

/-- PDF p.11, E3*, Eq.(24): expected monotonicity for a product of input states,
without replacing the input's entanglement by a sum of individual values. -/
theorem product_expected_monotonicity {n : ℕ} {I J : Fin n → Type}
    [∀ t, Fintype (I t)] [∀ t, Fintype (J t)]
    [∀ t, DecidableEq (I t)] [∀ t, DecidableEq (J t)]
    [∀ t, Nonempty (I t)] [∀ t, Nonempty (J t)]
    (sigma : ∀ t, Matrix (I t × J t) (I t × J t) ℂ)
    (hsigma : ∀ t, IsDensityMatrix (sigma t))
    {K : Type} [Fintype K]
    (L : K → Matrix (∀ t, I t) (∀ t, I t) ℂ)
    (R : K → Matrix (∀ t, J t) (∀ t, J t) ℂ) (hcomplete : ProductComplete L R) :
    let input := groupedStateProduct sigma
    let V := fun k => Matrix.kronecker (L k) (R k)
    (∑ k, if 0 < rectangularKrausProbability V input k then
      (rectangularKrausProbability V input k : EReal) * relativeEntanglementNats (normalizedBranch V input k)
      else 0) ≤ relativeEntanglementNats input := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P42

end
