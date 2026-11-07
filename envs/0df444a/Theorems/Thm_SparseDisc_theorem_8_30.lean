-- Prove2me | Theorems.Thm_SparseDisc_theorem_8_30
-- name    : SparseDisc.theorem_8_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:56:11.836204+00:00
-- url     : https://prove2.me/theorems/129a1c7e-2c1f-461c-b79e-40b582221472
-- title:
--   Theorem 8.30 — leveled orderings are good; $\mathrm{disc}(G) \le \max(2, \mathrm{dgn}(H(G)))$
-- statement:
--   1. Let $(G, \ell)$ be a leveled graph with all levels at least $2$, and suppose $V(G)$ can be ordered so that every vertex $v$ has at most $\ell_v$ later neighbours. Then $(G, \ell)$ is good.
--   2. Consequently, every 2-sparse instance $G$ satisfies
--   $$
--   \operatorname{disc}(G) \le \max(2, \operatorname{dgn}(H(G))) .
--   $$
--
--   This is the paper's main bound in the language of instances.
--
--   **Formalization Note** Orderings are injective ranks $r : V \to \mathbb N$.
--
--   Differences from the source:
--   - encoding: the item set [m] → a finite type of items; reason: Lean convention; [m] is the case Fin m, and every finite set is in bijection with some [m]
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Theorem 8.30, p.43

import Mathlib
import Definitions.Def_SparseDisc_IsLevelGood
import Definitions.Def_SparseDisc_laterNeighbours
import Definitions.Def_SparseDisc_degeneracy
import Definitions.Def_SparseDisc_IsInstance
import Definitions.Def_SparseDisc_IsTwoSparseSupp
import Definitions.Def_SparseDisc_instGraph
import Definitions.Def_SparseDisc_InstDiscLE

namespace SparseDisc

/-- **Theorem 8.30** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC
2027 submission manuscript (sha256 0f09ec60…25b81), p.43). Let `(G, ℓ)` be a leveled graph with all
levels at least 2, and suppose `V(G)` can be ordered so that every vertex `v` has at most `ℓ_v` later
neighbours. Then `(G, ℓ)` is good. Consequently, every 2-sparse instance `G` has
`disc(G) ≤ max(2, dgn(H(G)))`. -/
theorem theorem_8_30 :
    (∀ (V : Type) [Fintype V] (G : SimpleGraph V) (ℓ : V → ℕ), (∀ v, 2 ≤ ℓ v) →
      (∃ r : V → ℕ, Function.Injective r ∧ ∀ v, (laterNeighbours G r v).card ≤ ℓ v) →
      IsLevelGood G ℓ) ∧
    (∀ (V ι : Type) [Fintype V] [Fintype ι] [DecidableEq ι] (g : V → Cube ι → ℝ)
      (U : V → Finset ι), IsInstance g U → IsTwoSparseSupp U →
        InstDiscLE g ((max 2 (degeneracy (instGraph U)) : ℕ) : ℝ)) := by sorry

end SparseDisc
