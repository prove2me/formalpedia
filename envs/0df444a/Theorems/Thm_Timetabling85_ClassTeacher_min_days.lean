-- Prove2me | Theorems.Thm_Timetabling85_ClassTeacher_min_days
-- name    : Timetabling85.ClassTeacher.min_days
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:58.168829+00:00
-- url     : https://prove2.me/theorems/8769f0fe-fd23-4ef2-ac36-afed1719f616
-- title:
--   §2.1, p. 153 — the minimum number of days for CT2 is max(max_j ⌈Σ_i r_ij/b_j⌉, max_i ⌈Σ_j r_ij/a_i⌉)
-- statement:
--   Let $R=(r_{ij})$ be an $m\times n$ requirement matrix of nonnegative integers and $a_1,\dots,a_m$, $b_1,\dots,b_n$ positive integers. Put
--   $$p_{\min}=\max\Big(\max_j\Big\lceil \tfrac{\sum_{i=1}^m r_{ij}}{b_j}\Big\rceil,\ \max_i\Big\lceil \tfrac{\sum_{j=1}^n r_{ij}}{a_i}\Big\rceil\Big)$$
--   (an empty maximum being $0$). Then for every number of days $p$, problem CT2 with daily bounds $a_i$, $b_j$ has a solution over $p$ days if and only if $p\ge p_{\min}$.
--
--   So $p_{\min}$ days suffice and no smaller number of days does: $p_{\min}$ is the minimum number of days needed, as the paper states.
--
--   **Formalization Note** The "minimum" is stated as the equivalence "solvable over $p$ days iff $p\ge p_{\min}$", which says both that $p_{\min}$ is feasible and that every smaller $p$ is infeasible, without an `sInf` over a possibly empty set.
-- source:
--   de Werra, An introduction to timetabling, Eur. J. Oper. Res. 19 (1985), p. 153, §2.1, display for the minimum number of days p

import Mathlib
import Definitions.Def_Timetabling85_ClassTeacher_Problems

namespace Timetabling85.ClassTeacher

/-- The minimum number of days (de Werra 1985, §2.1, p. 153): for positive `a i`, `b j`, CT2 is
solvable over `p` days exactly when `p ≥ minDays R a b`. -/
theorem min_days {m n : ℕ} (R : Fin m → Fin n → ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (p : ℕ) :
    (∃ x : Fin m → Fin n → Fin p → ℕ, IsCT2 R p a b x) ↔ minDays R a b ≤ p := by sorry

end Timetabling85.ClassTeacher
