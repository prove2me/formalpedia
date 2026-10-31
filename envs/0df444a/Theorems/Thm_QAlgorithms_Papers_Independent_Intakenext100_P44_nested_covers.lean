-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P44_nested_covers
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P44.nested_covers
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:52:32.510109+00:00
-- url     : https://prove2.me/theorems/df5b5bfd-bcc6-46e2-ab9e-233033eee6b8
-- title:
--   Simultaneously nested countable covers with compact corner-manifold closures
-- statement:
--   Let $M$ be a connected finite-dimensional Hausdorff paracompact smooth manifold with corners, and let $(U_j)_{j\in J}$ be an open cover, with arbitrary index set $J$. There exist countable open covers $(V_i^\infty)_{i\in\mathbb N}$ and $(V_i^0)_{i\in\mathbb N}$ whose closures are compact manifolds with corners, with their subspace topologies, and such that
--
--   $$
--   \overline{V_i^\infty}\subseteq V_i^0\quad\text{for every }i.
--   $$
--
--   The family $(\overline{V_i^0})_i$ is locally finite and subordinate to the original cover: for every $i$ there is $j$ with $\overline{V_i^0}\subseteq U_j$.
--
--   After these endpoint covers have been chosen, let $L\subset(0,\infty)$ be any countable set. There is one simultaneous family $(V_i^\lambda)_i$, for $\lambda\in L\cup\{0,\infty\}$, agreeing with the prescribed endpoints. For each $\lambda\in L$ it is a countable locally finite open cover with compact corner-manifold closures. For all available parameters,
--
--   $$
--   0\le\mu<\lambda\le\infty
--   \quad\Longrightarrow\quad
--   \overline{V_i^\lambda}\subseteq V_i^\mu\quad\text{for every }i.
--   $$
--
--   These covers allow successive local changes with a margin between their domains. No global second-countability hypothesis is imposed.
-- source:
--   Equivalences of Smooth and Continuous Principal Bundles with Infinite-Dimensional Structure Group, arXiv:math/0604142v3, PDF p. 7, Proposition II.6: nested covers

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P44

open Set

open scoped ContDiff

/-- Proposition II.6, PDF pp. 7–8: endpoint covers are chosen before the arbitrary
countable positive set of intermediate parameters. All intermediate covers are
chosen simultaneously, with compact intrinsic corner-manifold closures and the
closure containment for every ordered pair of available parameters. -/
theorem nested_covers
    {M J : Type*} [TopologicalSpace M] [ConnectedSpace M]
    (d : ℕ) (a : CornerAtlas d M) (u : J → Set M)
    (hu : ∀ j, IsOpen (u j)) (hcover : ∀ x, ∃ j, x ∈ u j) :
    ∃ uinf u0 : ℕ → Set M,
      (∀ i, IsOpen (uinf i) ∧ IsOpen (u0 i) ∧
        IsCompact (closure (uinf i)) ∧ Nonempty (CornerAtlas d (closure (uinf i))) ∧
        IsCompact (closure (u0 i)) ∧ Nonempty (CornerAtlas d (closure (u0 i))) ∧
        closure (uinf i) ⊆ u0 i) ∧
      (∀ x, ∃ i, x ∈ uinf i) ∧ (∀ x, ∃ i, x ∈ u0 i) ∧
      LocallyFinite (fun i => closure (u0 i)) ∧
      (∀ i, ∃ j, closure (u0 i) ⊆ u j) ∧
      ∀ l : Set ℝ, l.Countable → (∀ r ∈ l, 0 < r) →
        ∃ v : WithTop ℝ → ℕ → Set M,
          v 0 = u0 ∧ v ⊤ = uinf ∧
          (∀ r ∈ l,
            (∀ i, IsOpen (v (r : WithTop ℝ) i) ∧
              IsCompact (closure (v (r : WithTop ℝ) i)) ∧
              Nonempty (CornerAtlas d (closure (v (r : WithTop ℝ) i)))) ∧
            (∀ x, ∃ i, x ∈ v (r : WithTop ℝ) i) ∧
            LocallyFinite (v (r : WithTop ℝ))) ∧
          (∀ mu lambda : WithTop ℝ,
            (mu = 0 ∨ mu = ⊤ ∨ ∃ r ∈ l, mu = (r : WithTop ℝ)) →
            (lambda = 0 ∨ lambda = ⊤ ∨ ∃ r ∈ l, lambda = (r : WithTop ℝ)) →
            mu < lambda → ∀ i, closure (v lambda i) ⊆ v mu i) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P44

end
