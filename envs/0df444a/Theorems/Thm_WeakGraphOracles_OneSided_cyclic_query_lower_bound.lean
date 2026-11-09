-- Prove2me | Theorems.Thm_WeakGraphOracles_OneSided_cyclic_query_lower_bound
-- name    : WeakGraphOracles.OneSided.cyclic_query_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:20:59.510117+00:00
-- url     : https://prove2.me/theorems/e76e21eb-eef9-4a2c-a6d8-3582457c313e
-- title:
--   Observation 1 — square-root lower bound for cyclic patterns
-- statement:
--   Let $H$ be a fixed connected finite simple graph containing a cycle. There is a positive proximity threshold $\epsilon_0$ such that, for every fixed $0<\epsilon\le\epsilon_0$, there are $c>0$ and $N\in\mathbb N$ for which every one-sided GEN1 $\epsilon$-tester on $n\ge N$ labels with worst-run query bound $q$ satisfies
--
--   $$q\ge c\sqrt n.$$
--
--   The tester has perfect completeness on every $H$-free graph and rejection probability at least $2/3$ on every graph requiring more than $\epsilon|E|$ deletions. The constants may depend on $H$ and the fixed proximity, but neither on $n$ nor on the tester. The source supplies no numerical Omega constant. This lower bound is the cyclic obstruction used in the singleton result and the family characterization.
--
--   Differences from the source:
--   - encoding: finite simple graphs with labels [n] → SimpleGraph (Fin n), with finite patterns carrying their own order; reason: relabeling by the standard bijection preserves every graph, appearance, degree and edge count
--   - encoding: adaptive randomized algorithms with at most q oracle queries → PMF over complete deterministic query plans of depth at most q, executed against fresh uniform response kernels; reason: finite query and reply alphabets at each fixed n and q make this equivalent to arbitrary internal randomization; no hidden graph is supplied to a policy
--   - encoding: Omega(n^(1/2)) at a fixed admissible proximity → a positive proximity interval, followed by positive c and a large-n threshold, all quantified before n and the tester; reason: makes the asymptotic dependencies explicit without inventing a numerical constant
--   - encoding: the edge query is undefined on an empty edge set in the displayed oracle description → a distinguished no-edge reply on edgeless inputs, and an isolation reply for empty neighbor sets; reason: completes the operational kernel on all input graphs, consistently with the source K2 discussion; nonempty-edge and neighbor laws are unchanged
-- source:
--   Oded Lachish, Amit Levi, Ilan Newman, Testability of General Graphs with Weak Query Oracles, STOC 2027 submission #274 (October 2026), p. 6 (PDF p. 7), Observation 1; proof p. 7 (PDF p. 8)

import Mathlib
import Definitions.Def_WeakGraphOracles_OneSided_testing

set_option autoImplicit false

namespace WeakGraphOracles.OneSided

/-- Observation 1, printed p.6 (PDF 7), with its proof on p.7.
The source supplies no numeric Omega constant. All constants precede n and A. -/
theorem cyclic_query_lower_bound (H : Pattern) (hH : EligiblePattern H)
    (hcycle : ¬ H.graph.IsAcyclic) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ (q : ℕ) (A : Policy n q),
          Correct {H} ε true (fun _ => True) EdgeFar A →
          c * Real.sqrt n ≤ q := by sorry

end WeakGraphOracles.OneSided
