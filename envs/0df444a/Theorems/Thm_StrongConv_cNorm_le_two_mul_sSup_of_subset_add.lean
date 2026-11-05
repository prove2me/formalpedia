-- Prove2me | Theorems.Thm_StrongConv_cNorm_le_two_mul_sSup_of_subset_add
-- name    : StrongConv.cNorm_le_two_mul_sSup_of_subset_add
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:37:59.381062+00:00
-- url     : https://prove2.me/theorems/8e353241-68c4-4eb2-a8da-e03f3a559116
-- title:
--   Lemma 4.2 — a polynomial is controlled by its values on an a/(4q²)-dense set
-- statement:
--   Let $h$ be a real polynomial of degree at most $q$, let $a > 0$, and let $I \subseteq [0, a]$ satisfy $[0, a] \subseteq I + [-\frac{a}{4q^2}, \frac{a}{4q^2}]$ (Minkowski sum). Then $\sup_{x \in [0,a]} |h(x)| \le 2 \sup_{x \in I} |h(x)|$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 15, Lemma 4.2 (interpolation), which applies Cheney, E. W., Introduction to approximation theory, AMS Chelsea (1998), Lemma 3(i), p. 91 (no DOI)

import Mathlib
import Definitions.Def_StrongConv

open Polynomial
open scoped Pointwise

namespace StrongConv

theorem cNorm_le_two_mul_sSup_of_subset_add (q : ℕ) (h : ℝ[X]) (hh : h.natDegree ≤ q) (a : ℝ)
    (ha : 0 < a) (I : Set ℝ) (hI : I ⊆ Set.Icc 0 a)
    (hdense : Set.Icc 0 a ⊆ I + Set.Icc (-(a / (4 * (q : ℝ) ^ 2))) (a / (4 * (q : ℝ) ^ 2))) :
    cNorm 0 (fun x => h.eval x) 0 a ≤ 2 * sSup ((fun x => |h.eval x|) '' I) := by
  sorry

end StrongConv
