-- Prove2me | Theorems.Thm_TwoAgentLateDP2004_LateLate_theorem_7_3
-- name    : TwoAgentLateDP2004.LateLate.theorem_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:49:57.45924+00:00
-- url     : https://prove2.me/theorems/54dfdeee-07a6-43ca-98bc-855cc06aac1c
-- title:
--   Theorem 7.3 — the DP computes the exact optimum in O(nA² nB + nA nB²) time
-- statement:
--   For every EDD-numbered real-valued instance $I$ and integer budget $Q$, execute the fixed bottom-up program. Write $n_A,n_B$ for its actual owner counts and $T(I,Q)$ for the charged execution cost. One absolute constant $c>0$, independent of sizes, job data, owners and $Q$, satisfies
--   $$T(I,Q)\le c(1+n)(1+n_A)(1+n_B),$$
--   $$n_A,n_B\ge1\quad\Longrightarrow\quad T(I,Q)\le8c(n_A^2n_B+n_An_B^2).$$
--   For $Q\ge0$, the derived counts and clipped budget are correct, every allocated table entry equals the independently defined $C(i,h,k)$, and clipping preserves $C(n,h,Q)$ for every $h$. The program returns infeasible exactly when no feasible full schedule exists. On every feasible input a finite final entry exists; the returned $h^*$ is
--   $$h^*=\min\{h\in\mathbb N:C(n,h,Q)<+\infty\},$$
--   is attained as the actual late-A count of a feasible full schedule, and is at most the actual late-A count of every feasible full schedule. The signed table makes negative $Q$ infeasible without casting it to zero.
--   This is both clauses of the source theorem: exact constrained optimality and its printed runtime rate. The operation count comes from the interpreted program, including allocation/initialization, owner counting, table writes and final scan; it is not merely a count of distinct recurrence arguments.
--
--   Differences from the source:
--   - generalization: two competing job sets with due dates and processing times → nonnegative real processing times, arbitrary real dates, and possibly empty owner classes; reason: no integrality restriction is imposed in §3; negative dates and empty classes extend the same formulas and include all source instances
--   - encoding: jobs and non-idling schedules on one machine → Fin n with an owner label and duplicate-free lists of all jobs; reason: each job belongs to exactly one agent; regular objectives permit removal of idle time without worsening either count
--   - reading: only C(0,0,0)=0 is printed → C(0,h,k)=0 for all nonnegative budgets; reason: the empty selected subset satisfies every at-most budget, forcing the unspecified zero row
--   - generalization: the minimum formula on a presupposed feasible instance and its asymptotic runtime → infeasibility equivalence for all integer Q and a padded finite bound, together with the exact positive-agent rate; reason: feasible source instances retain the same least value, attainment and lower bound; padding gives meaningful cost on empty axes
--   - encoding: C(n,h,Q) uses the original B budget → tabulation uses q=min(Q,nB) and the goal asserts equality with the original column; reason: late B counts cannot exceed nB; the equality is concluded, not assumed
--   - encoding: constant-time table operations and O(nA² nB+nA nB²) → finite oracle RAM execution with a single uniform c and positive-size multiplier 8; reason: each instruction and bind/return is charged; padded sizes imply the same printed asymptotic rate
--   - encoding: h* is the minimum finite final-column index → IsLeast over all natural h plus feasible attainment and the lower bound for every full schedule; reason: no empty infimum or caller-supplied optimum is used
--   - encoding: the dynamic program computes the least finite final-column index → one fixed bottom-up execution also certifies its computed owner counts and every allocated table cell against C, with signedC for signed indices; reason: makes the algorithm and the printed negative-index convention explicit; these execution properties are conclusions, never input certificates
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici (2004), Scheduling Problems with Two Competing Agents, Operations Research 52(2):229–242, https://doi.org/10.1287/opre.1030.0092, Theorem 7.3, p.236 (PDF p.8); standing model §3 pp.231–232

import Mathlib
import Definitions.Def_TwoAgentLateDP2004_LateLate_Program

namespace TwoAgentLateDP2004.LateLate

/-- Agnetis et al. (2004), Theorem 7.3, p.236 (PDF p.8), correctness AND runtime.
The same absolute c covers all sizes, numeric inputs, owner labels and integer Q.
The final positive-size bound is exactly the printed O(nA²nB+nAnB²) rate;
the padded bound additionally covers empty classes and the empty instance.
The RAM program, result, entire table and execution cost are independently defined.
No lemma, optimum, feasibility, clipping identity or time bound is assumed. -/
theorem theorem_7_3 : ∃ c : ℕ, 0 < c ∧
    ∀ {n : ℕ} (I : Input n) (Q : ℤ), Monotone I.d →
    let r := run I Q
    let a := ownerCount I true
    let b := ownerCount I false
    r.2.2 ≤ c * (1 + n) * (1 + a) * (1 + b) ∧
    (0 < a → 0 < b → r.2.2 ≤ (8 * c) * (a^2 * b + a * b^2)) ∧
    (0 ≤ Q →
      r.1.a = a ∧ r.1.b = b ∧ r.1.q = min Q.toNat b ∧
      (∀ i ≤ n, ∀ h ≤ a, ∀ k ≤ min Q.toNat b,
        r.2.1 (address (a+1) (min Q.toNat b+1) i h k) = C I i h k) ∧
      (∀ h, C I n h Q.toNat = C I n h (min Q.toNat b))) ∧
    (r.1.answer = none ↔ ¬ ∃ s, Feasible I Q s) ∧
    ((∃ s, Feasible I Q s) → ∃ h ≤ a, signedC I n h Q ≠ ⊤) ∧
    (∀ h, r.1.answer = some h →
      h ≤ a ∧ IsLeast {t : ℕ | signedC I n t Q ≠ ⊤} h ∧
      (∃ s, Feasible I Q s ∧ lateCount I true s = h) ∧
      (∀ s, Feasible I Q s → h ≤ lateCount I true s)) := by sorry

end TwoAgentLateDP2004.LateLate
