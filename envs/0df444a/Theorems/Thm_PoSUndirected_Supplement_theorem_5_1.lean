-- Prove2me | Theorems.Thm_PoSUndirected_Supplement_theorem_5_1
-- name    : PoSUndirected.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:36:11.281986+00:00
-- url     : https://prove2.me/theorems/456cf636-7d00-4f8d-85a6-4085367b5094
-- title:
--   Theorem 5.1 — exact universal stability factor $\max\{1,R^*(D)\}$
-- statement:
--   For every nonempty labelled demand multigraph $D$ after trivial demands are discarded, the least factor for which every optimum on every feasible positive-real-cost host is an approximate equilibrium is
--   $$
--   \max\{1,R^*(D)\}.
--   $$
--   The following are equivalent: $R^*(D)\le1$; every optimum is a weak equilibrium on every feasible host; every feasible host has ordinary price of stability one. Every optimum is strict on every host exactly when $R^*(D)<1$.
--
--   Replacing every labelled player by $k\ge1$ independent copies divides $R^*$ by $k$. Thus $\lceil R^*(D)\rceil$ is the exact weak replication threshold, and replicated optima are universally strict exactly when $k>R^*(D)$.
--
--   Differences from the source:
--   - encoding: an order of all terminal vertices → a permutation relative to an arbitrary fixed linear order on terminal labels; reason: every total order is represented exactly once and the maximum is independent of the reference order
--   - encoding: every finite feasible host → every `Fin n` host with an injective terminal embedding and arbitrary Steiner vertices; reason: every finite host is isomorphic to such a presentation
--   - encoding: $R^*(D)$ is a finite maximum → `sSup` of the order-value set under the explicit nonempty, nontrivial-demand hypothesis; reason: the set is finite, nonempty and bounded and each denominator is nonzero
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), Theorem 5.1, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_PoSUndirected_Supplement_RStar

set_option autoImplicit false

namespace PoSUndirected.Supplement

/-- **Theorem 5.1 (universal optimum stability).** Tsoufis, preprint sha256 c095d811…,
p.10 (PDF p.12).

For a nonempty labelled demand multigraph, `max 1 R⋆(D)` is the least universal approximate-
equilibrium factor for all optima on all feasible positive-cost hosts.  The `R⋆ ≤ 1`, universal
optimum equilibrium, and universal PoS-one conditions are equivalent; universal strictness is
equivalent to `R⋆ < 1`.  Replicating every labelled player `k` times divides `R⋆` by `k`, with
weak threshold `⌈R⋆⌉` and strict threshold `k > R⋆`.

**Formalization Note.** Terminal labels carry a fixed order solely to enumerate all permutations;
`RStar` maximizes over those permutations and is independent of that reference order.  Finite
hosts are standardized on `Fin n`, which covers every finite host up to relabelling and permits
Steiner vertices through the terminal embedding. -/
theorem theorem_5_1 {T ι : Type*} [Fintype T] [DecidableEq T] [LinearOrder T] [Nonempty T]
    [Fintype ι] [DecidableEq ι] (s t : ι → T) (hD : NonemptyDemand s t) :
    IsLeast {α : ℝ | UniversalOptimumApprox s t α} (max 1 (RStar s t)) ∧
    (RStar s t ≤ 1 ↔ UniversalOptimumEquilibrium s t) ∧
    (UniversalOptimumEquilibrium s t ↔ UniversalPoSOne s t) ∧
    (UniversalOptimumStrict s t ↔ RStar s t < 1) ∧
    (∀ k : ℕ, 1 ≤ k →
      RStar (replicatedSource s (k := k)) (replicatedTarget t (k := k)) = RStar s t / k) ∧
    (∀ k : ℕ, 1 ≤ k →
      (UniversalPoSOne (replicatedSource s (k := k)) (replicatedTarget t (k := k)) ↔
        RStar s t ≤ k)) ∧
    IsExactWeakReplicationThreshold s t ⌈RStar s t⌉₊ ∧
    (∀ k : ℕ, 1 ≤ k →
      (UniversalOptimumStrict (replicatedSource s (k := k)) (replicatedTarget t (k := k)) ↔
        RStar s t < k)) := by sorry

end PoSUndirected.Supplement
