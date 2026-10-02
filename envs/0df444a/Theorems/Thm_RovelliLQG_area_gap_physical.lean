-- Prove2me | Theorems.Thm_RovelliLQG_area_gap_physical
-- name    : RovelliLQG.area_gap_physical
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T19:30:33.021363+00:00
-- url     : https://prove2.me/theorems/e21ba9bb-9d35-4580-a67b-a53a6654192f
-- title:
--   Eq. (18): area gap in physical units $a_o=8\pi\hbar G\gamma\tfrac{\sqrt3}{2}$
-- statement:
--   Let $\gamma>0$ (Barbero–Immirzi parameter), $\hbar>0$ and $G>0$. Among the positive elements of the area spectrum
--   $$\mathcal A(\gamma,\hbar,G)=\Big\{8\pi\gamma\hbar G\sum_n\sqrt{j_n(j_n+1)}\Big\}$$
--   (finite families of half-integers $j_n\ge0$), the smallest is
--   $$a_o=8\pi\hbar G\gamma\,\frac{\sqrt3}{2}.$$
--
--   This is the area gap of eq. (13) in physical units, eq. (18) of the review, which uses $L_{\text{loop}}^2=8\pi\hbar G\gamma$ (eq. (17)).
-- source:
--   C. Rovelli, Loop quantum gravity: the first 25 years, Class. Quantum Grav. 28 (2011) 153002, doi:10.1088/0264-9381/28/15/153002, arXiv:1012.4707, §2.3, p. 9, eqs. (17)-(18), with the spectrum of eq. (26), §4.3, p. 16

import Mathlib
import Definitions.Def_RovelliLQG_Defs

open scoped InnerProductSpace

namespace RovelliLQG

theorem area_gap_physical (γ ħ G : ℝ) (hγ : 0 < γ) (hħ : 0 < ħ) (hG : 0 < G) :
    IsLeast {A ∈ areaSpectrum γ ħ G | 0 < A}
      (8 * Real.pi * ħ * G * γ * (Real.sqrt 3 / 2)) := by
  sorry

end RovelliLQG
