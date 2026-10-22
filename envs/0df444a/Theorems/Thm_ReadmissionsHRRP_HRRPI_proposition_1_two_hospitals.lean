-- Prove2me | Theorems.Thm_ReadmissionsHRRP_HRRPI_proposition_1_two_hospitals
-- name    : ReadmissionsHRRP.HRRPI.proposition_1_two_hospitals
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:08.334691+00:00
-- url     : https://prove2.me/theorems/dba45a9c-49f6-44a3-8535-c3d78d5fdd9c
-- title:
--   Proposition 1, p. 14 (N = 2) — with two hospitals every HRRP-I equilibrium is symmetric
-- statement:
--   Consider the hospital model under its standing assumptions, with the interior-first-best hypothesis, and exactly two hospitals paid by HRRP-I, so that each hospital's yardsticks are the other's actions: $\bar c_1=c_2$, $\bar r_1=r_2$, $\bar R_1=R(r_2,c_2)$, and symmetrically. If $\big((r_1,c_1),(r_2,c_2)\big)$ is a pure-strategy Nash equilibrium, then
--   $$(r_1,c_1)=(r_2,c_2).$$
--
--   So with two hospitals there is no asymmetric equilibrium, and the symmetric equilibria of the existence and ordering claims are all the equilibria.
--
--   **Formalization Note** The two hospitals are indexed by `Fin 2`; an asymmetric equilibrium would be one with different actions at the two indices.
-- source:
--   Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the right incentives: Issues and remedies, author-accepted manuscript, LBS Research Online eprint 1402 (Management Science 67(4), 2021, doi:10.1287/mnsc.2020.3649), p. 14, Proposition 1 (second sentence)

import Mathlib
import Definitions.Def_ReadmissionsHRRP_HRRPI_Setting

namespace ReadmissionsHRRP.HRRPI

/-- Proposition 1 (p. 14), two hospitals: with `N = 2` every HRRP-I equilibrium is symmetric. -/
theorem proposition_1_two_hospitals (M : Model) (hM : M.Standing) (hA : M.FirstBestInterior) :
    ∀ x : Fin 2 → ℝ × ℝ, M.IsEqI 2 x → x 0 = x 1 := by sorry

end ReadmissionsHRRP.HRRPI
