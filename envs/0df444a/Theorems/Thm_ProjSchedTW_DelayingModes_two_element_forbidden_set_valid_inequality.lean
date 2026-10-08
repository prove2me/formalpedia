-- Prove2me | Theorems.Thm_ProjSchedTW_DelayingModes_two_element_forbidden_set_valid_inequality
-- name    : ProjSchedTW.DelayingModes.two_element_forbidden_set_valid_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T23:05:45.628126+00:00
-- url     : https://prove2.me/theorems/970ac3c2-4424-423b-a71e-4a08800ef437
-- title:
--   §2.5.2, Eq. (2.5.7) — valid temporal constraint from an unresolved two-element forbidden set
-- statement:
--   Let $UB\in\mathbb Z$ and let $d_{ij}$ be the longest path lengths in $N^+$ with $\delta_{n+1,0}=-UB$. Let $\{i,j\}$ be a two-element forbidden set ($i\ne j$, $r_{ik}+r_{jk}>R_k$ for some $k$) for which neither $d_{ij}>-p_j$ nor $d_{ji}>-p_i$ holds. Then for all activities $h,l\in V$ and every feasible schedule $S$ with $S_{n+1}\le UB$,
--   $$S_l\ \ge\ S_h+\min\bigl(d_{hi}+p_i+d_{jl},\ d_{hj}+p_j+d_{il}\bigr).\qquad(2.5.7)$$
--
--   Although neither order of $i$ and $j$ is forced, one of them must precede the other in every feasible schedule; the inequality combines both possibilities into a single temporal constraint, which preprocessing adds as a new arc $\langle h,l\rangle$ of $N^+$ whenever it is stronger than $d_{hl}$.
--
--   **Formalization Note.** Distances take values in `WithBot ℝ` with `⊥` for $-\infty$; a term containing $-\infty$ is $-\infty$, and then the inequality is trivially satisfied, as in the book's convention. The hypothesis "neither $d_{ij}>-p_j$ nor $d_{ji}>-p_i$" is the case in which the page states the inequality. The standing assumptions of the model are hypotheses.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 55, §2.5.2, Eq. (2.5.7)

import Mathlib
import Definitions.Def_ProjSchedTW_DelayingModes_Project
import Definitions.Def_ProjSchedTW_DelayingModes_Distance

namespace ProjSchedTW.DelayingModes

theorem two_element_forbidden_set_valid_inequality {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (hP : P.StandingAssumptions) (UB : ℤ) (i j : Fin (n + 2)) (hij : i ≠ j)
    (hF : P.IsForbidden {i, j})
    (hij_not : ¬ (((-(P.p j : ℝ) : ℝ) : WithBot ℝ) < P.distPlus UB i j))
    (hji_not : ¬ (((-(P.p i : ℝ) : ℝ) : WithBot ℝ) < P.distPlus UB j i))
    (S : Fin (n + 2) → ℝ) (hS : P.IsFeasible S) (hUB : S (Fin.last (n + 1)) ≤ UB)
    (h l : Fin (n + 2)) :
    min (P.distPlus UB h i + ((P.p i : ℝ) : WithBot ℝ) + P.distPlus UB j l)
        (P.distPlus UB h j + ((P.p j : ℝ) : WithBot ℝ) + P.distPlus UB i l)
      ≤ ((S l - S h : ℝ) : WithBot ℝ) := by sorry

end ProjSchedTW.DelayingModes
