-- Prove2me | Theorems.Thm_RovelliLQG_areaSpectrum_discrete
-- name    : RovelliLQG.areaSpectrum_discrete
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T19:31:34.339006+00:00
-- url     : https://prove2.me/theorems/88a87f49-1853-4cad-8dfe-fa41f466685b
-- title:
--   Eq. (26): the area spectrum of loop gravity is discrete
-- statement:
--   Let $\gamma,\hbar,G>0$. The area spectrum
--   $$\mathcal A(\gamma,\hbar,G)=\Big\{A=8\pi\gamma\hbar G\sum_n\sqrt{j_n(j_n+1)}\ :\ \text{finite families of half-integers } j_n\ge0\Big\}$$
--   is discrete in the strong sense that for every $R\in\mathbb R$ only finitely many of its elements satisfy $A\le R$.
--
--   This is the review's claim that "the area of surfaces in space ... [has a] discrete spectrum", with the spectrum given by eq. (26).
-- source:
--   C. Rovelli, Loop quantum gravity: the first 25 years, Class. Quantum Grav. 28 (2011) 153002, doi:10.1088/0264-9381/28/15/153002, arXiv:1012.4707, §4.3, p. 16, eq. (26)

import Mathlib
import Definitions.Def_RovelliLQG_Defs

open scoped InnerProductSpace

namespace RovelliLQG

theorem areaSpectrum_discrete (γ ħ G : ℝ) (hγ : 0 < γ) (hħ : 0 < ħ) (hG : 0 < G)
    (R : ℝ) : {A ∈ areaSpectrum γ ħ G | A ≤ R}.Finite := by
  sorry

end RovelliLQG
