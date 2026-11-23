-- Prove2me | Theorems.Thm_SethiChengSS_Finite_Supplement_theorem_5_1
-- name    : SethiChengSS.Finite.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:27:59.658387+00:00
-- url     : https://prove2.me/theorems/04bb9666-86a4-4df2-a6f6-93dd501a0539
-- title:
--   Theorem 5.1 — calendar restrictions
-- statement:
--   Fix the finite-horizon model of §2, a terminal period $N$, and any deterministic calendar of allowed ordering dates. Assume (4.1), $K_n^i\ge\sum_jp_{ij}K_{n+1}^j\ge0$, and (4.2), the upper-coercivity assumption. There are state-dependent thresholds $s_n^i\le S_n^i$, allowing the no-order case $s_n^i=-\infty$, such that
--   $$\widehat u_n(i,x)=\begin{cases}(S_n^i-x)\delta(s_n^i-x),&\text{ordering is allowed at }n,\\0,&\text{otherwise}.\end{cases}$$
--   The rule is in $B_0$, is feasible and attains the calendar DP minimum at every state and every real surplus. For every starting period $n\le N$, state $i$ and surplus $x$, its generated history-dependent policy is admissible and
--   $$J_n(i,x;\widehat U)=v_n^{\mathrm{cal}}(i,x)=\inf_{U\ \mathrm{calendar\ admissible}}J_n(i,x;U).$$
--   Here the middle real DP value is embedded in $[0,\infty]$. The statement explicitly includes the comparison with every admissible history-dependent policy, the identity (4.9) with (5.1), and the nonemptiness, lower boundedness and integrability that justify the DP operations.
--
--   This is the no-ordering-period companion to the published finite-horizon optimality theorem; fixed costs in forbidden periods remain the stored data used in (4.1).
--
--   **Formalization Note** Extended thresholds satisfy $S\ne+\infty$ and $s\ne-\infty\Rightarrow S\ne-\infty$. The result holds on the full real surplus domain and every subproblem, including the terminal period. No order is charged at period $N$.
--
--   Differences from the source:
--   - reading: The theorem continues the §4 model and its induction. → Standing, (4.1) and (4.2) are explicit, and the calendar is arbitrary and state independent. reason: The proof on pp. 935–936 modifies only the feasible action dates, retaining K in forbidden periods.
--   - encoding: An optimal (s,S) feedback policy in the constrained inventory problem. → Both DP attainment and equality to the infimum over all measurable history-dependent policies are explicit, using extended no-order thresholds and the published path law. reason: This preserves the operational optimality meaning and Remark 4.4, including every initial subproblem; integrability and bounded-infimum conclusions certify total operations.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, p. 935, Theorem 5.1; proof continues on p. 936

import Mathlib
import Definitions.Def_SethiChengSS_Finite_Supplement_Calendar

namespace SethiChengSS.Finite.Supplement

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Theorem 5.1, pp. 935–936: arbitrary no-ordering dates, with both DP attainment
and optimality over the constrained history-dependent policy class. -/
theorem theorem_5_1 {L : ℕ} (D : Data L) (N : ℕ) (allowed : ℕ → Prop)
    (hD : Standing D) (h41 : Cond41 D N) (h42 : Cond42 D N) :
    ∃ s S : ℕ → Fin L → EReal,
      (∀ n < N, ∀ i, s n i ≤ S n i ∧ S n i ≠ ⊤ ∧ (s n i ≠ ⊥ → S n i ≠ ⊥)) ∧
      (∀ n < N, InB0 (calendarRule allowed s S n)) ∧
      (∀ n < N, ∀ i x,
        (calendarObjective D n (calendarV D allowed N (n + 1)) i x ''
          calendarActions allowed n).Nonempty ∧
        BddBelow (calendarObjective D n (calendarV D allowed N (n + 1)) i x ''
          calendarActions allowed n) ∧
        calendarRule allowed s S n i x ∈ calendarActions allowed n ∧
        calendarV D allowed N n i x = D.f n i x - D.c n i * x + calendarH D allowed N n i x ∧
        calendarV D allowed N n i x = D.f n i x +
          calendarObjective D n (calendarV D allowed N (n + 1)) i x
            (calendarRule allowed s S n i x) ∧
        ∀ u ∈ calendarActions allowed n,
          calendarObjective D n (calendarV D allowed N (n + 1)) i x
            (calendarRule allowed s S n i x) ≤
          calendarObjective D n (calendarV D allowed N (n + 1)) i x u) ∧
      (∀ n < N, ∀ i j y,
        Integrable (fun z => calendarV D allowed N (n + 1) j (y - z) * D.φ n i z)
          (volume.restrict (Set.Ioi 0))) ∧
      (∀ n ≤ N, ∀ i x,
        CalendarAdmissible allowed N n (feedback (calendarRule allowed s S) n x) ∧
        0 ≤ calendarV D allowed N n i x ∧
        J D N n i x (feedback (calendarRule allowed s S) n x) =
          ENNReal.ofReal (calendarV D allowed N n i x) ∧
        calendarValue D allowed N n i x = ENNReal.ofReal (calendarV D allowed N n i x) ∧
        ∀ U : Policy L, CalendarAdmissible allowed N n U →
          J D N n i x (feedback (calendarRule allowed s S) n x) ≤ J D N n i x U) := by sorry

end SethiChengSS.Finite.Supplement
