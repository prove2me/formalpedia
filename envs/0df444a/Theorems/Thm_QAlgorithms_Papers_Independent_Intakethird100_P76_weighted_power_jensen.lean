-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P76_weighted_power_jensen
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P76.weighted_power_jensen
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T09:18:11.488824+00:00
-- url     : https://prove2.me/theorems/be6e92b5-1805-473b-964a-b481af6011c4
-- title:
--   Lemma 8 (finite weighted power Jensen inequality)
-- statement:
--   Let $J$ be a finite index set and let $\lambda_j,a_j\ge0$ satisfy $\sum_{j\in J}\lambda_j=1$. For every real $r\ge1$,
--   $$\left(\sum_{j\in J}\lambda_j a_j\right)^r\le\sum_{j\in J}\lambda_j a_j^r.$$
--
--   This finite weighted Jensen inequality is used for the conditional power moment in the leakage analysis.
-- source:
--   The Sender-Excited Secret Key Agreement Model: Capacity, Reliability and Secrecy Exponents, arXiv:1107.4148v4, PDF p. 15, Lemma 8 (finite weighted power Jensen inequality)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P76

namespace QAlgorithms.Papers.Independent.Intakethird100.P76

noncomputable section

open scoped BigOperators

open Filter Set

attribute [local instance] Classical.propDecidable

-- Exact pinned primitives, inspected at their definitions before reuse.

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

variable {S X Y Z : Type} [Fintype S] [Fintype X] [Fintype Y] [Fintype Z]
  [Nonempty S] [Nonempty X] [Nonempty Y] [Nonempty Z]

variable {n u w : ℕ}

/-- PDF p.15, Lemma 8: finite weighted power Jensen. The sum=1 hypothesis
excludes an empty index type automatically. -/
theorem weighted_power_jensen {J : Type*} [Fintype J] (weights values : J → ℝ)
    (hweights : ∀ j, 0 ≤ weights j) (hvalues : ∀ j, 0 ≤ values j)
    (hsum : ∑ j, weights j = 1) (r : ℝ) (hr : 1 ≤ r) :
    (∑ j, weights j * values j) ^ r ≤ ∑ j, weights j * (values j) ^ r := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P76
