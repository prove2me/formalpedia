-- Prove2me | Theorems.Thm_SubnormalCover_isUniformCover_mul_mem_biUnion
-- name    : SubnormalCover.isUniformCover_mul_mem_biUnion
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-14T12:45:29.56805+00:00
-- url     : https://prove2.me/theorems/5904f2ff-83bb-46d4-92a1-fc89ff95a9dd
-- title:
--   A partial union in a uniform cover is a union of cosets
-- statement:
--   Let $A=\{a_iG_i\}_{i=1}^{k}$ be a **uniform cover** of a group $G$ by left cosets, i.e. the covering function $w_A(x)=|\{i : x\in a_iG_i\}|$ is a constant $w$. Sun's Lemma 4.1 introduces $K_A=\{x\in G: w_A(gx)=w_A(g)\ \forall g\in G\}$ and shows that for any $I\subseteq\{1,\dots,k\}$ the set $\bigcup_{i\in I}a_iG_i$ is a union of left cosets of $K_A\cap\bigcap_{j\notin I}G_j$; for a uniform cover $w_A$ is constant, so $K_A=G$ and the conclusion becomes that $\bigcup_{i\in I}a_iG_i$ is a union of left cosets of $\bigcap_{j\notin I}G_j$. This is the form used in the proof of Theorem 4.1, where $I=\{i : p_r\mid n_i\}$.
--
--   **Formalization note.** 'Is a union of left cosets of $\bigcap_{j\notin I}G_j$' is rendered equivalently as stability under right multiplication: if $x\in\bigcup_{i\in I}a_iG_i$ and $y\in\bigcap_{j\notin I}G_j$ then $xy\in\bigcup_{i\in I}a_iG_i$. The index subset is a `Set (Fin k)` (so $I^{c}$ is set complement and no `DecidableEq` is needed) and the intersection is the subgroup-valued `⨅ j ∈ Iᶜ, K j`, which is `⊤` when $I$ is everything.
-- source:
--   Z.-W. Sun, On the Herzog-Schönheim conjecture for uniform covers of groups, J. Algebra 273 (2004) 153-175, https://doi.org/10.1016/S0021-8693(03)00526-X, Lemma 4.1, eq. (4.1) (specialised to uniform covers, where $K_A = G$); p. 164–165

import Mathlib
import Definitions.Def_SubnormalCover_uniformCover

open Pointwise

namespace SubnormalCover

theorem isUniformCover_mul_mem_biUnion {G : Type*} [Group G] {k : ℕ}
    (K : Fin k → Subgroup G) (a : Fin k → G) (w : ℕ) (hcov : IsUniformCover K a w)
    (I : Set (Fin k)) {x y : G}
    (hx : x ∈ ⋃ i ∈ I, (a i) • (K i : Set G))
    (hy : y ∈ ⨅ j ∈ Iᶜ, K j) :
    x * y ∈ ⋃ i ∈ I, (a i) • (K i : Set G) := by
  sorry

end SubnormalCover
