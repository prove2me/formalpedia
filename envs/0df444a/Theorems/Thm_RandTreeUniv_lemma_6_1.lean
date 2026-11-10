-- Prove2me | Theorems.Thm_RandTreeUniv_lemma_6_1
-- name    : RandTreeUniv.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:10:25.076067+00:00
-- url     : https://prove2.me/theorems/e563f3c6-dafc-44ee-86cd-f23e899ecd11
-- title:
--   Lemma 6.1 (Montgomery) — splitting a tree into two subtrees sharing one vertex
-- statement:
--   For every tree $T$ and every set of vertices $Q\subseteq V(T)$ there are trees $T_1,T_2$ intersecting in a single vertex such that $T=T_1\cup T_2$ and
--
--   $$
--   \min\{|V(T_1)\cap Q|,\ |V(T_2)\cap Q|\}\ge|Q|/3 .
--   $$
--
--   This is Proposition 3.19 of Montgomery (2019). Applied three times with $Q=V(T)$ it yields the four-tree decomposition of §6.
--
--   Differences from the source:
--   - encoding: trees T₁, T₂ with T = T₁ ∪ T₂ intersecting in one vertex → vertex sets W₁, W₂ whose induced subgraphs are connected, W₁ ∩ W₂ = {x}, every vertex and edge of T inside W₁ or W₂; reason: a connected subgraph of a tree is the induced subgraph on its vertex set
--   - encoding: |V(Tᵢ) ∩ Q| ≥ |Q|/3 → |Q| ≤ 3·|Wᵢ ∩ Q| in ℕ; reason: same inequality
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), Lemma 6.1, p.30 (PDF 31) (Proposition 3.19 in Montgomery 2019)

import Mathlib

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- **Lemma 6.1** (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), p.30 (PDF 31); Proposition 3.19 in Montgomery 2019). For every tree `T`
and every set of vertices `Q ⊆ V(T)`, there are trees `T₁, T₂` intersecting in a single vertex
such that `T = T₁ ∪ T₂` and `min{|V(T₁) ∩ Q|, |V(T₂) ∩ Q|} ≥ |Q|/3`.

**Formalization Note** `T₁`, `T₂` are given by their vertex sets `W₁`, `W₂`; each `T_i` is the
subgraph of `T` induced on `W_i`, required to be connected (hence a tree). `T = T₁ ∪ T₂` means
every vertex and every edge of `T` lies in `T₁` or `T₂`. The bound `|V(T_i) ∩ Q| ≥ |Q|/3` is
`|Q| ≤ 3 |W_i ∩ Q|`. -/
theorem lemma_6_1 {V : Type*} [Fintype V] (T : SimpleGraph V) (hT : T.IsTree) (Q : Finset V) :
    ∃ (W₁ W₂ : Finset V) (x : V),
      (T.induce (W₁ : Set V)).Connected ∧ (T.induce (W₂ : Set V)).Connected ∧
      W₁ ∩ W₂ = {x} ∧ (∀ v, v ∈ W₁ ∨ v ∈ W₂) ∧
      (∀ u v, T.Adj u v → (u ∈ W₁ ∧ v ∈ W₁) ∨ (u ∈ W₂ ∧ v ∈ W₂)) ∧
      Q.card ≤ 3 * (W₁ ∩ Q).card ∧ Q.card ≤ 3 * (W₂ ∩ Q).card := by sorry

end RandTreeUniv
