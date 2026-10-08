-- Prove2me | Theorems.Thm_SingleMachinePrec_ConvexBipartite_lemma_A_1
-- name    : SingleMachinePrec.ConvexBipartite.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:42:17.17328+00:00
-- url     : https://prove2.me/theorems/c450bef5-4637-4f20-b19a-651bfd66945d
-- title:
--   Lemma A.1 — $E_1, E_2, E_3$ partition $\mathrm{inc}(P)$ and none contains a pair together with its reverse
-- statement:
--   Let $\mathbf P = (N, P)$ be a convex bipartite order and let $E_1, E_2, E_3$ be the sets of incomparable pairs defined in the Appendix. Then:
--
--   1. the sets $E_1, E_2, E_3$ form a partition of $\mathrm{inc}(\mathbf P)$: a pair $(x,y)$ is incomparable if and only if it lies in $E_1 \cup E_2 \cup E_3$, and the three sets are pairwise disjoint;
--   2. for every $(x, y) \in \mathrm{inc}(\mathbf P)$ and every $m \in \{1,2,3\}$,
--   $$
--   (x,y) \in E_m \implies (y,x) \notin E_m .
--   $$
--
--   Part 2 ensures that no $\bar E_m$ forces both orders of an incomparable pair, and part 1 that every incomparable pair is placed in some $\bar E_m$ in the direction it will be reversed.
--
--   **Formalization Note** "Partition" is read as covering plus pairwise disjointness; some of the $E_m$ may be empty (for instance $E_3 = \emptyset$ when there are no plus jobs). No numbering assumption on the plus jobs is used.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 668, Lemma A.1

import Mathlib
import Definitions.Def_SingleMachinePrec_ConvexBipartite_IncPartition

namespace SingleMachinePrec.ConvexBipartite

open ConvexBipartiteOrder

/-- Lemma A.1 (Ambühl et al. 2011, p. 668). For a convex bipartite order:
(i) `E₁, E₂, E₃` form a partition of `inc(P)` — every incomparable pair lies in one of them,
each of them consists of incomparable pairs, and they are pairwise disjoint;
(ii) for every incomparable pair `(x, y)` and every `m ∈ {1, 2, 3}`, if `(x, y) ∈ E_m` then
`(y, x) ∉ E_m`. -/
theorem lemma_A_1 {a b : ℕ} (C : ConvexBipartiteOrder a b) :
    ((∀ x y : Job a b, SingleMachinePrec.Framework.Incomparable C.prec x y ↔ (C.E1 x y ∨ C.E2 x y ∨ C.E3 x y)) ∧
      (∀ x y : Job a b, ¬ (C.E1 x y ∧ C.E2 x y)) ∧
      (∀ x y : Job a b, ¬ (C.E1 x y ∧ C.E3 x y)) ∧
      (∀ x y : Job a b, ¬ (C.E2 x y ∧ C.E3 x y))) ∧
    (∀ x y : Job a b, SingleMachinePrec.Framework.Incomparable C.prec x y →
      (C.E1 x y → ¬ C.E1 y x) ∧ (C.E2 x y → ¬ C.E2 y x) ∧ (C.E3 x y → ¬ C.E3 y x)) := by sorry

end SingleMachinePrec.ConvexBipartite
