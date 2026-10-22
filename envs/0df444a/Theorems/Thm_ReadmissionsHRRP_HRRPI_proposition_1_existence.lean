-- Prove2me | Theorems.Thm_ReadmissionsHRRP_HRRPI_proposition_1_existence
-- name    : ReadmissionsHRRP.HRRPI.proposition_1_existence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:04.661499+00:00
-- url     : https://prove2.me/theorems/98a0b3a9-da9b-4b93-bbe9-2718def0f1b3
-- title:
--   Proposition 1, p. 14 (existence) — under HRRP-I at least one symmetric equilibrium (r̃, c̃) exists
-- statement:
--   Consider the hospital model under its standing assumptions, with the interior-first-best hypothesis, and $N\ge 2$ hospitals paid by the HRRP-I transfer
--   $$T_i=\bar c_i\lambda(1+r_i)-\frac{1}{\bar r_i}(r_i-\bar r_i)(1+r_i)\bar c_i\lambda+\bar R_i .$$
--   Then there is a point $(\tilde r,\tilde c)$ such that the profile in which every hospital plays $(\tilde r,\tilde c)$ is a pure-strategy Nash equilibrium of the game in which each hospital maximizes its profit $\Pi_i=T_i-c_i(1+r_i)\lambda-R(r_i,c_i)$ over the box.
--
--   Existence makes the ordering claim of Proposition 1 non-vacuous, and the symmetric equilibrium is the object studied in the rest of §4.
--
--   **Formalization Note** The equilibrium action lies in the box (this is part of the equilibrium definition). $N\ge2$ is needed for the averages of (6) to be defined.
-- source:
--   Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the right incentives: Issues and remedies, author-accepted manuscript, LBS Research Online eprint 1402 (Management Science 67(4), 2021, doi:10.1287/mnsc.2020.3649), p. 14, Proposition 1 (first clause)

import Mathlib
import Definitions.Def_ReadmissionsHRRP_HRRPI_Setting

namespace ReadmissionsHRRP.HRRPI

/-- Proposition 1 (p. 14), existence: with `N ≥ 2` hospitals, HRRP-I has a symmetric
equilibrium `(r̃, c̃)`. -/
theorem proposition_1_existence (M : Model) (hM : M.Standing) (hA : M.FirstBestInterior)
    (N : ℕ) (hN : 2 ≤ N) :
    ∃ p : ℝ × ℝ, M.IsSymEqI N p := by sorry

end ReadmissionsHRRP.HRRPI
