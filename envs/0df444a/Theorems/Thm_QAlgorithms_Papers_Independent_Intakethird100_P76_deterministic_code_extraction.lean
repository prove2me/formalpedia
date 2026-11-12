-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P76_deterministic_code_extraction
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P76.deterministic_code_extraction
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T09:18:58.672558+00:00
-- url     : https://prove2.me/theorems/f80146c1-f4f2-474c-9a67-4ce599067be4
-- title:
--   §VII-C, unnumbered simultaneous deterministic-code extraction
-- statement:
--   Let $\mathcal C$ be a finite ensemble with nonnegative masses $p(c)$ summing to one. Let $e(c),\ell(c)\ge0$ be its realized-code error and leakage statistics. A code in the support simultaneously satisfies
--   $$p(c_*)>0,\qquad e(c_*)\le3\sum_c p(c)e(c),\qquad \ell(c_*)\le3\sum_c p(c)\ell(c).$$
--   The statement holds for arbitrary nonnegative statistics, including zero ensemble means.
--
--   It supplies a deterministic simultaneous selection with finite factor 3. It does not supply the separate entropy-rate condition or finite-block exponential bounds with prefactor one.
-- source:
--   The Sender-Excited Secret Key Agreement Model: Capacity, Reliability and Secrecy Exponents, arXiv:1107.4148v4, PDF p. 15, §VII-C, unnumbered simultaneous deterministic-code extraction

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

/-- PDF pp.15--16: simultaneous extraction from one finite ensemble.
Printed: strict <3*mean bounds and dotted exponential-order comparisons.
Changed: weak <=3*mean bounds with positive ensemble mass. Why: zero mean
forces zero on support, so strict <3*0 is impossible. The finite factor 3 is
retained; no finite-block exponent prefactor one or entropy claim is added. -/
theorem deterministic_code_extraction {C : Type*} [Fintype C]
    (p e l : C → ℝ) (hp : IsLaw p) (he : ∀ c, 0 ≤ e c) (hl : ∀ c, 0 ≤ l c) :
    ∃ c, 0 < p c ∧ e c ≤ 3 * (∑ d, p d * e d) ∧
      l c ≤ 3 * (∑ d, p d * l d) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P76
