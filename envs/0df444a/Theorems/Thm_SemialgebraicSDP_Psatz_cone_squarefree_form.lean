-- Prove2me | Theorems.Thm_SemialgebraicSDP_Psatz_cone_squarefree_form
-- name    : SemialgebraicSDP.Psatz.cone_squarefree_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:44.077414+00:00
-- url     : https://prove2.me/theorems/db23acdc-e34f-4855-b0f7-4d15488d5477
-- title:
--   Proof of Theorem 5.1 — $f=p_0+p_1f_1+\dots+p_{12\dots s}f_1\cdots f_s$ with SOS $p_T$
-- statement:
--   Let $f_1,\dots,f_s\in\mathbb R[x_1,\dots,x_n]$. A polynomial $f$ belongs to the cone $P(\{f_1,\dots,f_s\})$ if and only if it can be written with one sum-of-squares multiplier per squarefree product of the $f_j$:
--   $$
--   f=\sum_{T\subseteq\{1,\dots,s\}} p_T\prod_{j\in T}f_j = p_0+p_1f_1+\dots+p_sf_s+p_{12}f_1f_2+\dots+p_{12\dots s}f_1\cdots f_s,
--   $$
--   with every $p_T$ a sum of squares (the empty product being $1$).
--
--   This is the parameterization of the cone part of a Positivstellensatz certificate used to set up the SDP in the proof of Theorem 5.1: it reduces the search over the cone to finitely many sum-of-squares unknowns.
-- source:
--   Parrilo, Semidefinite programming relaxations for semialgebraic problems, Math. Program. Ser. B 96 (2003) 293–320, p. 306, proof of Theorem 5.1, display 'f = p₀ + p₁f₁ + ⋯'

import Mathlib
import Definitions.Def_SemialgebraicSDP_Psatz_Cone

namespace SemialgebraicSDP.Psatz

open MvPolynomial

theorem cone_squarefree_form {n s : ℕ} (f : Fin s → MvPolynomial (Fin n) ℝ)
    (x : MvPolynomial (Fin n) ℝ) :
    x ∈ cone (Set.range f) ↔
      ∃ p : Finset (Fin s) → MvPolynomial (Fin n) ℝ,
        (∀ T, IsSumSq (p T)) ∧ x = ∑ T : Finset (Fin s), p T * ∏ j ∈ T, f j := by sorry

end SemialgebraicSDP.Psatz
