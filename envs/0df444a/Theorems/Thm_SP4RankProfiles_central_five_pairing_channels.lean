-- Prove2me | Theorems.Thm_SP4RankProfiles_central_five_pairing_channels
-- name    : SP4RankProfiles.central_five_pairing_channels
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-08T04:04:58.091303+00:00
-- url     : https://prove2.me/theorems/e6bfecd7-3d31-4d6b-95d9-9f46c0e6f200
-- title:
--   Central-rank-five finite cancellation channels
-- statement:
--   Let $g>0$ be an integer and give eight atoms the filtration levels $(g,g,0,0,0,0,-g,-g)$ and arbitrary integer degree labels $M_i$. Suppose they carry a complete graded cancellation pairing: an involutive bijection $p$, a Boolean source label $s$, opposite source labels on partners, and strictly lower filtration and degree exactly one lower at the partner of every source. Then
--
--   $$
--   s(0)=s(1)=\mathrm{true},\qquad p(0),p(1)\in\{2,3,4,5\},
--   $$
--
--   $$
--   s(6)=s(7)=\mathrm{false},\qquad p(6),p(7)\in\{2,3,4,5\}.
--   $$
--
--   Because the partner map is an involutive bijection, these are exactly two top-to-center and two center-to-bottom pairs. No direct top-to-bottom pairing remains.
--
--   This is a theorem about actual finite pairing data. The permanent ninth atom is not encoded, and existence of a compatible cancellation pairing for a given differential or HFK group is not established. No height bound beyond $g>0$ follows; a height-one pairing exists in this model.
-- source:
--   Ryan Shin, corrected unpublished gt_e12_rank18_cube_attack.md, Section 2, equation (2.1) and Section 2.1; SHA-256 ac06bc38602b5eb920f798ed749c06e06f56430eb0151d213ca2650834ccb883. Only the indicated finite rank-profile and pairing arguments are formalized; no HFK construction or external genus-one classification theorem is supplied.

import Definitions.Def_SP4RankProfiles
import Definitions.Def_SP4RankNine

set_option autoImplicit false

open SP4RankProfiles

theorem SP4RankProfiles.central_five_pairing_channels (g : ℤ) (hg : 0 < g) (M : Fin 8 → ℤ)
    (P : SP4RankNine.CancellationPairing (centralFiveLevel g) M) :
    (∀ i : Fin 8, i.val < 2 →
      P.source i = true ∧ 2 ≤ (P.mate i).val ∧ (P.mate i).val < 6) ∧
    (∀ i : Fin 8, 6 ≤ i.val →
      P.source i = false ∧ 2 ≤ (P.mate i).val ∧ (P.mate i).val < 6) := by sorry
