-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P40_single_letter_sum_rate_bound
-- name    : QAlgorithms.Papers.Independent.Next46.P40.single_letter_sum_rate_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:55:32.408374+00:00
-- url     : https://prove2.me/theorems/99aef989-de42-4ae7-9f89-c5c5130dab9b
-- title:
--   Additional single-letter sum-rate bound
-- statement:
--   Let $\mathcal M:A'B'\to C$ be a memoryless CPTP channel between finite nonzero registers, with independent sender–receiver entanglement and maximum-error classical capacity region $C_E(\mathcal M)$. For independent normalized purifications $\phi_1^{AA'}$ and $\phi_2^{BB'}$, write $\theta=(\mathrm{id}_{AB}\otimes\mathcal M)(\phi_1\otimes\phi_2)$. There is a maximizing product input, independent of the rate pair, and every $(R_1,R_2)\in C_E(\mathcal M)$ satisfies
--
--   $$R_1+R_2\le\max_{\rho_1,\rho_2} I(AB;C)_\theta.$$
--
--   The maximum ranges over separate one-use density operators, with arbitrary rank, not over entangled joint inputs. This gives an additional single-letter restriction even though the full region is regularized.
-- source:
--   Entanglement-Assisted Capacity of Quantum Multiple-Access Channels, arXiv:quant-ph/0511228v2, PDF p. 7, (45); proof (52) on p.8

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Next46.P40

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation marginalRB associate)

variable {A B C E R S : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype R] [Fintype S]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E]

variable [DecidableEq R] [DecidableEq S]

/-- PDF p.7, (45), proved with one-use product marginals on p.8, (52).
The maximum is attained over PRODUCT inputs, never entangled joint inputs.
The maximizer is selected before any capacity-region rate pair. -/
theorem single_letter_sum_rate_bound
    [Nonempty A] [Nonempty B] [Nonempty C]
    (M : Superop (A × B) C) (hM : IsChannel M) :
    ∃ (v : EuclideanSpace ℂ (A × A)) (w : EuclideanSpace ℂ (B × B)),
      ‖v‖ = 1 ∧ ‖w‖ = 1 ∧
      (∀ (v2 : EuclideanSpace ℂ (A × A)) (w2 : EuclideanSpace ℂ (B × B)),
        ‖v2‖ = 1 → ‖w2‖ = 1 →
        mutualInformation (qmacTheta M v2 w2) ≤ mutualInformation (qmacTheta M v w)) ∧
      ∀ r ∈ eaMacCapacityRegion M, r.1 + r.2 ≤ mutualInformation (qmacTheta M v w) := by sorry

end QAlgorithms.Papers.Independent.Next46.P40

end
