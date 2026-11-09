-- Prove2me | Theorems.Thm_QuadraticProbe717_Insertion_square_difference_multiplicity
-- name    : QuadraticProbe717.Insertion.square_difference_multiplicity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:20.867972+00:00
-- url     : https://prove2.me/theorems/f5f6d7fc-efa6-49f0-8b9c-be3c1c269cd3
-- title:
--   Lemma 6.2 — square-difference multiplicity
-- statement:
--   For every $\eta>0$ there is $C_\eta>0$ such that, for every odd prime $n$ and every integer $1<k\le n/2$,
--   $$R(k)\le C_\eta\left(\frac{k^2}{n}+n^{1/2+\eta}\right).$$
--   The maximum defining $R(k)$ is over all nonzero residues. The coefficient is uniform in $n$ and $k$; the error exponent is quantified rather than replaced by one fixed exponent.
--
--   Differences from the source:
--   - reading: uniform big-O and n^{1/2+o(1)} → for every η>0 there is Cη>0 before all instance quantifiers, bounding the main term plus n^{1/2+η}; reason: constants depend only on η; finite exceptions are absorbed in Cη
--   - encoding: k≤n/2 → 2k≤n on natural indices; reason: equivalent integer endpoint, including the source boundary
-- source:
--   Yang S. Hu, William Kuszmaul, Jingxun Liang, Stefan Walzer, Huacheng Yu, Renfei Zhou, STOC 2027 submission #717 (October 2026), Lemma 6.2, p. 12 (PDF p. 12)

import Definitions.Def_QuadraticProbe717_Insertion_arithmetic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace QuadraticProbe717.Insertion

theorem square_difference_multiplicity :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) [NeZero n], n.Prime → Odd n →
      ∀ k : ℕ, 1 < k → 2 * k ≤ n →
        (multiplicity n k : ℝ) ≤ C * ((k : ℝ)^2 / n + (n : ℝ) ^ (1 / 2 + η)) := by sorry

end QuadraticProbe717.Insertion
