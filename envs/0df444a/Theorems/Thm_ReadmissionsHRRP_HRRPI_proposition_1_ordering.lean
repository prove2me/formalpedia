-- Prove2me | Theorems.Thm_ReadmissionsHRRP_HRRPI_proposition_1_ordering
-- name    : ReadmissionsHRRP.HRRPI.proposition_1_ordering
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:05.239049+00:00
-- url     : https://prove2.me/theorems/686931d5-c5d9-4055-ad6f-39a543f6bdc1
-- title:
--   Proposition 1, p. 14 (ordering) — every symmetric HRRP-I equilibrium has r̃ < r* and c̃ > c*
-- statement:
--   Consider the hospital model under its standing assumptions, with the interior-first-best hypothesis, and $N\ge 2$ hospitals paid by HRRP-I. Let $(\tilde r,\tilde c)$ be any symmetric equilibrium and $(r^*,c^*)$ any maximizer of the welfare $S$ over the box. Then
--   $$\tilde r<r^*\qquad\text{and}\qquad \tilde c>c^* .$$
--
--   In words, hospitals over-invest in readmission reduction and under-invest in cost reduction relative to the first best; the paper attributes this to the multiplier $(1+r_i)/\bar r_i$ in the HRRP penalty.
--
--   **Formalization Note** The statement quantifies over every maximizer of $S$; by Lemma 1 there is exactly one, $(r^*,c^*)$. Both inequalities are strict, as on the page.
-- source:
--   Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the right incentives: Issues and remedies, author-accepted manuscript, LBS Research Online eprint 1402 (Management Science 67(4), 2021, doi:10.1287/mnsc.2020.3649), p. 14, Proposition 1 (first sentence)

import Mathlib
import Definitions.Def_ReadmissionsHRRP_HRRPI_Setting

namespace ReadmissionsHRRP.HRRPI

/-- Proposition 1 (p. 14), ordering: every symmetric HRRP-I equilibrium `(r̃, c̃)` satisfies
`r̃ < r*` and `c̃ > c*`, where `(r*, c*)` is the maximizer of the welfare `S` over the box. -/
theorem proposition_1_ordering (M : Model) (hM : M.Standing) (hA : M.FirstBestInterior)
    (N : ℕ) (hN : 2 ≤ N) :
    ∀ p : ℝ × ℝ, M.IsSymEqI N p →
      ∀ xs : ℝ × ℝ, M.IsFirstBest xs → p.1 < xs.1 ∧ xs.2 < p.2 := by sorry

end ReadmissionsHRRP.HRRPI
