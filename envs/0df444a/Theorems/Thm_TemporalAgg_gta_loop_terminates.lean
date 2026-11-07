-- Prove2me | Theorems.Thm_TemporalAgg_gta_loop_terminates
-- name    : TemporalAgg.gta_loop_terminates
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:57.079775+00:00
-- url     : https://prove2.me/theorems/73916951-8558-4f69-9ecf-90619b8b118a
-- title:
--   §3.1, p.16 — the loop of GTA terminates, whatever pairs are chosen
-- statement:
--   Fix the current time $t$. Each iteration of the loop of Greedy Temporal Aggregation moves two nonempty groups into the group of $t$. Then:
--
--   1. there is no infinite sequence of loop iterations at time $t$, starting from any state and choosing any candidate pairs;
--   2. from every state, some finite sequence of iterations reaches a stable state (one with no candidate pair).
--
--   Termination is what makes GTA an algorithm: every time step ends, and the "every run" statements of Lemmas 3.1–3.3 are not vacuous.
--
--   **Formalization Note** The first clause is well-foundedness of the converse of one loop iteration, on pairs of a state and a sample counter. Both clauses are stated for arbitrary states, not only for those reachable in a run.
--
--   Differences from the source:
--   - reading: while there exist time steps t₁ ≠ t₂ whose groups differ in size by at most a factor of 2 (Algorithm 1, p.16) → both groups nonempty, sizes a, b with a ≤ 2b and b ≤ 2a; reason: two empty groups would satisfy the condition forever, contradicting 'so the loop terminates' and 'the sizes of any two nonempty groups differ by more than a factor of 2' (p.16)
--   - generalization: the loop terminates (at each time step, from the state after the adversary's samples) → MergeStep t is well-founded on all pairs (state, counter), and from every state a Stable state is reachable; reason: the loop's starting states are among all states, so the statement specializes to the paper's
--   - encoding: groups of time steps; 'sample all objects of both groups' → a state last : Fin n → ℕ (time of each object's current realization); a merge sends both groups to the current time t and adds the two group sizes to a counter; reason: the group of s is {u | last u = s}; the same states and moves
-- source:
--   Haeupler, Paramonov, Temporal Aggregation: Maintaining Randomness against Adaptive Adversaries, STOC 2027 submission (manuscript of 2026-11-03, sha256 42ebf866…), §3.1, p.16

import Mathlib
import Definitions.Def_TemporalAgg_IsGTARun

namespace TemporalAgg

/-- **Termination of the GTA loop** (Haeupler, Paramonov, *Temporal Aggregation: Maintaining Randomness against Adaptive
Adversaries*, STOC 2027 submission, manuscript of 2026-11-03, sha256 42ebf866…, §3.1, p.16: "Each iteration of the loop moves the two
groups into the group of the current time t (one of t1, t2 may be t itself), so the loop
terminates.").

1. At every time `t`, there is no infinite sequence of loop iterations from any state, whatever
   pairs are chosen: the relation `MergeStep t` is well-founded (read backwards).
2. Consequently, from every state some finite sequence of iterations reaches a state in which the
   loop condition fails (`Stable`).

**Formalization Note** The states are arbitrary `(last, counter)` pairs, not only reachable
ones. -/
theorem gta_loop_terminates {n : ℕ} (t : ℕ) :
    WellFounded (fun b a : (Fin n → ℕ) × ℕ => MergeStep t a b) ∧
      ∀ a : (Fin n → ℕ) × ℕ, ∃ b, Relation.ReflTransGen (MergeStep t) a b ∧ Stable b.1 := by sorry

end TemporalAgg
