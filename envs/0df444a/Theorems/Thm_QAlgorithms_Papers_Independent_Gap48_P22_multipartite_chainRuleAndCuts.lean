-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P22_multipartite_chainRuleAndCuts
-- name    : QAlgorithms.Papers.Independent.Gap48.P22.multipartite_chainRuleAndCuts
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:20:03.854302+00:00
-- url     : https://prove2.me/theorems/00fc825a-84e8-4166-80ed-1dcd52e02ee5
-- title:
--   Total conditional information: ordered-tail chain rule and all cuts
-- statement:
--   Let $n\ge2$ and let $\rho^{A_1\cdots A_nE}$ be a normalized state on finite positive-dimensional systems. All reductions below come from this one state, and entropy is in bits. Define the total conditional information, without a factor of one half, by $I(A_1:\cdots:A_n\mid E)=\sum_i S(A_iE)-S(A_1\cdots A_nE)-(n-1)S(E)$. Then
--
--   $$I(A_1:\cdots:A_n\mid E)=\sum_{i=1}^{n-1}I(A_i:A_{i+1}\cdots A_n\mid E).$$
--
--   For every $\varepsilon\ge0$, if this total is at most $2\varepsilon$, then every singleton cut and every subset cut satisfy
--
--   $$I(A_i:A_{[n]\setminus\{i\}}\mid E)\le2\varepsilon,\qquad I(A_J:A_{[n]\setminus J}\mid E)\le2\varepsilon\quad(J\subseteq[n]).$$
--
--   Empty grouped registers are one-dimensional. This chain rule controls all grouped bipartitions of the same extension while retaining its conditioning register.
-- source:
--   Squashed entanglement, k-extendibility, quantum Markov chains, and recovery maps, arXiv:1410.4184v4, PDF p. 11, Appendix: chain rule and bipartitions

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

/-- Appendix, PDF p.11: ordered-tail chain rule and every singleton/subset cut
bound of the same normalized extension. The empty/full cut is allowed. -/
theorem multipartite_chainRuleAndCuts {n : ℕ} (hn : 2 ≤ n)
    {D : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    {E : Type} [Fintype E] [Nonempty E]
    (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (hrho : IsDensityMatrix rho) :
    conditionalMultipartiteInformation .total rho (singleParties n) ∅ =
      ∑ i : Fin (n-1), groupedCMI rho {⟨i.val, by omega⟩}
        (Finset.univ.filter fun j => i.val < j.val) ∧
    (∀ epsilon : ℝ, 0 ≤ epsilon →
      conditionalMultipartiteInformation .total rho (singleParties n) ∅ ≤ 2 * epsilon →
      (∀ i : Fin n, groupedCMI rho {i} (Finset.univ.erase i) ≤ 2 * epsilon) ∧
      ∀ s : Finset (Fin n), groupedCMI rho s sᶜ ≤ 2 * epsilon) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P22

end
