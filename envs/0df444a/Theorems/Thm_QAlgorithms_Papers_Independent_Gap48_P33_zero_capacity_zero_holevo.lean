-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P33_zero_capacity_zero_holevo
-- name    : QAlgorithms.Papers.Independent.Gap48.P33.zero_capacity_zero_holevo
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:48:26.028113+00:00
-- url     : https://prove2.me/theorems/aa43ee4e-b850-4172-b5ae-85c03821af29
-- title:
--   zero von Neumann capacity implies zero classical Holevo information
-- statement:
--   Let $\mathcal N$ be a CPTP map between finite nonzero registers, and suppose its maximum reference-output mutual information over normalized inputs is zero. For every finite probability vector $w_j$ and every finite family of normalized input densities $\rho_j$,
--
--   $$\chi\!\left(\{w_j,\mathcal N(\rho_j)\}\right)=S\!\left(\sum_jw_j\mathcal N(\rho_j)\right)-\sum_jw_jS(\mathcal N(\rho_j))=0.$$
--
--   Consequently the maximum, and hence supremum, over all finite single-use input ensembles is zero. This uses the paper's Holevo convention for classical information; it invokes no later operational coding identification.
-- source:
--   On the von Neumann capacity of noisy quantum channels, arXiv:quant-ph/9609024v3, PDF p. 14, VII, unnumbered: zero von Neumann capacity implies zero classical Holevo information

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P33

namespace QAlgorithms.Papers.Independent.Gap48.P33

open scoped BigOperators Matrix ComplexConjugate

-- Reuse only definitions from the pinned accepted library; no imported theorem is used.

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average labelInformation)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation first both)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange inputMutualInfo)

open QAlgorithms.Papers.Independent.Claimed50.P03 (pauliWeight wordSupport)

section FiniteRegisters

variable {A B C D R K J : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [Fintype R] [Fintype K] [Fintype J]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq R] [DecidableEq K] [DecidableEq J]

/-- PDF pp.14–15, VII: zero maximum unmeasured information forces every finite
output Holevo ensemble to vanish. This is a single-use Holevo maximum, not an
operational coding theorem. -/
theorem zero_capacity_zero_holevo
    [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N)
    (hzero : IsGreatest (informationValues N) 0) :
    (∀ (m : ℕ) (w : Fin m → ℝ), ProbabilityWeights w →
      ∀ rho : Fin m → Matrix A A ℂ, (∀ j, IsDensityMatrix (rho j)) →
        labelInformation w (fun j => N (rho j)) = 0) ∧
    IsGreatest {z : ℝ | ∃ (m : ℕ) (w : Fin m → ℝ) (rho : Fin m → Matrix A A ℂ),
      ProbabilityWeights w ∧ (∀ j, IsDensityMatrix (rho j)) ∧
        z = labelInformation w (fun j => N (rho j))} 0 := by sorry

end FiniteRegisters

end QAlgorithms.Papers.Independent.Gap48.P33
