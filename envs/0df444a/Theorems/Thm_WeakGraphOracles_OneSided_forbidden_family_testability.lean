-- Prove2me | Theorems.Thm_WeakGraphOracles_OneSided_forbidden_family_testability
-- name    : WeakGraphOracles.OneSided.forbidden_family_testability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:21:19.966201+00:00
-- url     : https://prove2.me/theorems/ab501580-c4fb-4bcc-90f6-4260247af570
-- title:
--   Theorem 8 — family characterization (corrected: empty forbidden family)
-- statement:
--   Let $F$ be a finite family of connected finite simple graphs, each with at least one and at most a fixed $k$ edges. The input graphs are arbitrary finite simple graphs on known, unbounded $n$. Then
--
--   $$\operatorname{Test}_{\mathrm{GEN1}}(F)\iff
--   F=\varnothing\ \lor\left[(\exists T\in F,\ T\text{ is a tree})\ \land\ \forall h\in\mathbb N,\operatorname{Test}_{\mathrm{RN},h}(F)\right].$$
--
--   GEN1 supplies independent uniform random edges and random neighbors, and uses minimum deletions strictly greater than $\epsilon|E(G)|$. The RN side supplies only random neighbors on the promise of $h$-degeneracy and uses minimum deletions strictly greater than $\epsilon n$. Both accept all free inputs with probability one and reject every far input with probability at least $2/3$. For each fixed $\epsilon>0$ (and fixed $h$ for RN), one finite worst-run query bound works for every $n$, with a graph-independent policy at each $n$. No time or uniform-computability bound is imposed.
--
--   Thus the empty family is testable; every nonempty family with no tree is not testable; GEN1 testability of a tree-containing family implies RN testability for every fixed degeneracy; and the latter condition implies GEN1 testability. The arbitrary input is not assumed degenerate, covered by appearances or role preserving. This is the full qualitative characterization, rather than an assumed cleaning or simulation result.
--
--   Differences from the source:
--   - correction: the no-tree clause says every finite family containing no tree is not testable → the empty family is explicitly testable, and the original obstruction applies to every nonempty tree-free family; reason: F=empty satisfies all printed member assumptions and contains no tree, but every graph is free and the zero-query always-accept policy is perfect; all nonempty-family clauses and both directions are retained
--   - encoding: a family of finite size connected graphs, under the §4.1 assumption of at most k edges and no isolated vertex → Finset Pattern whose members are connected with between 1 and k edges; reason: connected graphs with at most k edges and no isolated vertex form finitely many isomorphism classes, and freeness and distance depend only on those classes
--   - encoding: finite simple graphs with labels [n] → SimpleGraph (Fin n), with finite patterns carrying their own order; reason: relabeling by the standard bijection preserves every graph, appearance, degree and edge count
--   - encoding: adaptive randomized algorithms with at most q oracle queries → PMF over complete deterministic query plans of depth at most q, executed against fresh uniform response kernels; reason: finite query and reply alphabets at each fixed n and q make this equivalent to arbitrary internal randomization; no hidden graph is supplied to a policy
--   - encoding: minimum number of actual edge deletions, with strict farness → ENNReal infimum of cardinalities of feasible deletion sets; comparison with ENNReal.ofReal of epsilon times the edge or vertex count; reason: the feasible family is finite and nonempty for the stated patterns, so the infimum is its attained integer minimum; empty feasible families have value infinity, never a fabricated zero
--   - encoding: the edge query is undefined on an empty edge set in the displayed oracle description → a distinguished no-edge reply on edgeless inputs, and an isolation reply for empty neighbor sets; reason: completes the operational kernel on all input graphs, consistently with the source K2 discussion; nonempty-edge and neighbor laws are unchanged
-- source:
--   Oded Lachish, Amit Levi, Ilan Newman, Testability of General Graphs with Weak Query Oracles, STOC 2027 submission #274 (October 2026), p. 9 (PDF p. 10), Theorem 8; proof pp. 17–18 (PDF pp. 18–19); §§1.1, 3, 4.1 standing assumptions

import Mathlib
import Definitions.Def_WeakGraphOracles_OneSided_testing

set_option autoImplicit false

namespace WeakGraphOracles.OneSided

/-- Theorem 8 (corrected: empty forbidden family), printed p.9 (PDF 10).
The empty family is a concrete exception to the printed no-tree clause:
all graphs are free, and the zero-query always-accept policy is perfect.
Every nonempty-family clause and both directions are retained. -/
theorem forbidden_family_testability (F : Finset Pattern) (k : ℕ)
    (hF : AdmissibleFamily F k) :
    GEN1Testable F ↔
      F = ∅ ∨ ((∃ T ∈ F, T.graph.IsTree) ∧ ∀ h : ℕ, RNTestable F h) := by sorry

end WeakGraphOracles.OneSided
