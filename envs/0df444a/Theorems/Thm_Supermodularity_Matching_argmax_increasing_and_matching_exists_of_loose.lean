-- Prove2me | Theorems.Thm_Supermodularity_Matching_argmax_increasing_and_matching_exists_of_loose
-- name    : Supermodularity.Matching.argmax_increasing_and_matching_exists_of_loose
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T21:21:50.148997+00:00
-- url     : https://prove2.me/theorems/3190ba85-32d9-4f2b-9a95-30848f846719
-- title:
--   Theorem 3.2.1 — loose labor market: increasing optimal hiring and an increasing optimal matching
-- statement:
--   Suppose the labor market is loose, so each firm's hiring decision is an unconstrained
--   maximization over the whole product lattice $\prod_{i=1}^n X_i$ of worker qualities, and
--   suppose the profit function $f(x,j)$ is supermodular in the joint variable $(x,j)$ on
--   $\bigl(\prod_{i=1}^n X_i\bigr) \times \{1,\dots,m\}$ (with $\{1,\dots,m\}$ ordered as a
--   chain, so `SupermodularOn` applies to the product lattice). Then:
--
--   1. the set of profit-maximizing hiring decisions for firm $j$,
--      $$\operatorname*{arg\,max}_{x \in \prod_i X_i} f(x,j),$$
--      is increasing in $j$ with respect to the induced set ordering $\sqsubseteq$
--      (`InducedSetOrder`): for $j \le k$, $\operatorname{argmax}(\cdot,j) \sqsubseteq
--      \operatorname{argmax}(\cdot,k)$; and
--   2. there exists an increasing optimal matching (`IsIncreasingMatching` and
--      `IsOptimalMatching`).
--
--   Topkis, Theorem 3.2.1 (p. 98): "If the labor market is loose and $f(x,j)$ is supermodular in
--   $(x,j)$ on $\times_{i=1}^n X_i \times \{1,\dots,m\}$, then the set of optimal hiring
--   decisions $\operatorname{argmax}_{x\in\times_{i=1}^n X_i} f(x,j)$ for each firm $j$ is
--   increasing with respect to the induced set ordering $\sqsubseteq$ in $j$ and there exists an
--   increasing optimal matching." The theorem follows from Theorem 2.8.2 and Theorem 2.8.3 of
--   Chapter 2 (mission II of this series), applied firm by firm.
--
--   **Formalization Note.** A *loose* labor market is exactly one in which each firm's hiring
--   problem is the unconstrained maximization $\max_{x\in\prod_i X_i} f(x,j)$ (Topkis, p. 96,
--   equation (3.2.2)); this is represented structurally by using the general, unconstrained
--   `IsOptimalMatching` predicate (which already maximizes over every matching with no supply
--   constraint) rather than by adding a separate Boolean "loose" hypothesis. Existence of a
--   nonempty maximizer for each firm, needed for the induced-set-order conclusion to be
--   meaningful, follows from `[∀ i, Fintype (X i)]` and `[∀ i, Nonempty (X i)]` and need not be
--   assumed separately.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 98, Theorem 3.2.1

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_Supermodularity_Matching_IsOptimalMatching
import Definitions.Def_Supermodularity_Matching_IsIncreasingMatching

namespace Supermodularity.Matching

theorem argmax_increasing_and_matching_exists_of_loose
    {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)] [∀ i, Fintype (X i)]
    [∀ i, Nonempty (X i)]
    (f : (∀ i, X i) → Fin m → ℝ)
    (hf : Supermodularity.Monotonicity.SupermodularOn
      (fun p : (∀ i, X i) × Fin m => f p.1 p.2) Set.univ)
    (hloose : ∀ x : Fin m → ∀ i, X i,
        IsOptimalMatching f x ↔ ∀ j : Fin m, ∀ y : ∀ i, X i, f y j ≤ f (x j) j) :
    (∀ ⦃j k : Fin m⦄, j ≤ k →
        Supermodularity.Lattices.InducedSetOrder
          {x : ∀ i, X i | ∀ y : ∀ i, X i, f y j ≤ f x j}
          {x : ∀ i, X i | ∀ y : ∀ i, X i, f y k ≤ f x k}) ∧
      ∃ x : Fin m → ∀ i, X i, IsIncreasingMatching x ∧ IsOptimalMatching f x := by sorry

end Supermodularity.Matching
