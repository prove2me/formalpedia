-- Prove2me | Theorems.Thm_TwoOptAllExp_TSP_Supplement_lemma_23
-- name    : TwoOptAllExp.TSP.Supplement.lemma_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:50:32.862429+00:00
-- url     : https://prove2.me/theorems/00751600-a39c-49e9-acfc-2521d9ab569b
-- title:
--   Lemma 23 — $D_n$ is acyclic, has unique source $1$, and every vertex reaches $T_n$
-- statement:
--   For every $n\ge0$ the dependency graph $D_n$ on the positions $1,\dots,T_n$:
--
--   1. is acyclic;
--   2. has $1$ as its unique source (the only position with no incoming edge);
--   3. every position $k\in\{1,\dots,T_n\}$ can reach $T_n$ by a directed path.
--
--   Differences from the source:
--   - encoding: D_n acyclic → no position k has a nonempty directed path (TransGen) from k to k; reason: nonempty directed cycles are forbidden; all listed edge endpoints lie in [T_n], so the remaining natural numbers are isolated and add no cycles
--   - encoding: unique source 1 → for 1 ≤ k ≤ T_n: k has no incoming edge iff k = 1; reason: sources among the vertices [T_n]
--   - encoding: every vertex can reach T_n → ReflTransGen of the edge relation from every k ∈ [T_n] to T_n; reason: reachability, T_n reaching itself trivially
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, Lemma 23, p. 32

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Supplement_MCA232

namespace TwoOptAllExp.TSP.Supplement

open MCA232 MCA232.Vx

/-- **Lemma 23** (p. 32). The graph `D_n` is acyclic, has unique source `1`, and every vertex can
reach `T_n`. -/
theorem lemma_23 (n : ℕ) :
    (∀ k : ℕ, ¬ Relation.TransGen (DAdj n) k k) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ T n → ((∀ r : ℕ, ¬ DAdj n r k) ↔ k = 1)) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ T n → Relation.ReflTransGen (DAdj n) k (T n)) := by sorry

end TwoOptAllExp.TSP.Supplement
