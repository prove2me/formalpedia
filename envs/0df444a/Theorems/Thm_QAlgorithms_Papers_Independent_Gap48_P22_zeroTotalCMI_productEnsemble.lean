-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P22_zeroTotalCMI_productEnsemble
-- name    : QAlgorithms.Papers.Independent.Gap48.P22.zeroTotalCMI_productEnsemble
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:20:57.551843+00:00
-- url     : https://prove2.me/theorems/54eb11f8-feef-4fbc-badb-2597f12b305a
-- title:
--   An exact zero-information extension yields a product ensemble
-- statement:
--   Let $n\ge2$ and let $\rho^{A_1\cdots A_nE}$ be a density operator on finite positive-dimensional systems. Suppose this actual extension has zero total conditional information in bits:
--
--   $$\sum_{i=1}^nS(A_iE)-S(A_1\cdots A_nE)-(n-1)S(E)=0.$$
--
--   There are a finite index set $\Lambda$, nonnegative probabilities $p_\lambda$ summing to one, and local density operators $\rho_{\lambda,i}^{A_i}$ such that
--
--   $$\operatorname{Tr}_E\rho=\sum_{\lambda\in\Lambda}p_\lambda\bigotimes_{i=1}^n\rho_{\lambda,i}^{A_i}.$$
--
--   Thus the marginal is fully separable, with an actual product-state ensemble. This concerns a zero-information extension and does not assert faithfulness of an infimum over extensions.
-- source:
--   Squashed entanglement, k-extendibility, quantum Markov chains, and recovery maps, arXiv:1410.4184v4, PDF p. 12, Appendix: exact zero case (pp.11–12)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Gap48.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P12 (squashedEntanglement KExtendible)

open QAlgorithms.Papers.Independent.Claimed50.P33
  (RegisterBasis registerMarginal entropyAt conditionalMultipartiteInformation singleParties
   forgetEnvironment)

open QAlgorithms.Papers.Independent.Renew46.P35 (classicalCMI)

open QAlgorithms.Entanglement (IsSeparableDensity)

/-- Appendix, PDF pp.11–12: an actual zero-total-information extension yields
an actual finite product-state ensemble of its marginal. This spells out the
witnesses of Claimed50.P33.IsMixedFullySeparable without a bundled-state cast.
It does not assert faithfulness of the multipartite infimum. -/
theorem zeroTotalCMI_productEnsemble {n : ℕ} (hn : 2 ≤ n)
    {D : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    {E : Type} [Fintype E] [Nonempty E]
    (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (hrho : IsDensityMatrix rho)
    (hzero : conditionalMultipartiteInformation .total rho (singleParties n) ∅ = 0) :
    ∃ l : ℕ, ∃ p : Fin l → ℝ,
      ∃ r : (j : Fin l) → (i : Fin n) → Matrix (D i) (D i) ℂ,
        (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧
        (∀ j i, IsDensityMatrix (r j i)) ∧
        ∀ a b, forgetEnvironment rho a b = ∑ j, (p j : ℂ) * ∏ i, r j i (a i) (b i) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P22

end
