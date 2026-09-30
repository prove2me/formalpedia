-- Prove2me | Theorems.Thm_SP4RankProfiles_rank_nine_raw_profiles
-- name    : SP4RankProfiles.rank_nine_raw_profiles
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-08T04:01:33.789295+00:00
-- url     : https://prove2.me/theorems/0e487ca2-aad5-4526-ac90-ad25f88728c2
-- title:
--   Complete symmetric rank-nine profile enumeration
-- statement:
--   Let $r:\mathbb Z\to\mathbb N$ be finitely supported with total mass nine. Assume $r(-a)=r(a)$ for every integer $a$, $r(0)>0$, every off-central value $r(a)$ is even, and at least one off-central value is nonzero. Then its nonzero ranks are exactly one of
--
--   $$
--   (2,5,2)\text{ at }(-g,0,g),\quad (4,1,4)\text{ at }(-g,0,g),\quad (2,2,1,2,2)\text{ at }(-g,-h,0,h,g),
--   $$
--
--   with $g>0$ in the three-level alternatives and $0<h<g$ in the five-level alternative. In each case every unlisted value is zero. The conclusion asserts exhaustion by these existential alternatives; uniqueness of the parameters is not a separate conclusion.
--
--   The support shape is derived, not assumed. This is the full raw numerical enumeration, not knot classification. Excluding the four-one-four profile or forcing adjacent five-level heights requires separate graded-pairing arguments. The central-five height-one case remains possible under these hypotheses.
-- source:
--   Ryan Shin, corrected unpublished gt_e12_rank18_cube_attack.md, Section 2, equation (2.1) and Section 2.1; SHA-256 ac06bc38602b5eb920f798ed749c06e06f56430eb0151d213ca2650834ccb883. Only the indicated finite rank-profile and pairing arguments are formalized; no HFK construction or external genus-one classification theorem is supplied.

import Definitions.Def_SP4RankProfiles

set_option autoImplicit false

open SP4RankProfiles

theorem SP4RankProfiles.rank_nine_raw_profiles (r : ℤ →₀ ℕ)
    (htotal : mass r = 9) (hsym : ∀ a, r (-a) = r a)
    (hcenter : 0 < r 0) (heven : ∀ a, a ≠ 0 → Even (r a))
    (hnontrivial : ∃ a, a ≠ 0 ∧ 0 < r a) :
    (∃ g : ℤ, 0 < g ∧ r = three g 2 5) ∨
    (∃ g : ℤ, 0 < g ∧ r = three g 4 1) ∨
    (∃ g h : ℤ, 0 < h ∧ h < g ∧ r = five g h) := by sorry
