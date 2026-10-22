-- Prove2me | Theorems.Thm_SidB_weakly_norming_bound
-- name    : SidB.weakly_norming_bound
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-21T21:26:37.546335+00:00
-- url     : https://prove2.me/theorems/93cd0f13-ed26-4f99-a9c7-8d576c936c27
-- title:
--   The weak-norming bound for the chain hypergraph (Lemma 3.3)
-- statement:
--   Lemma 3.3 of the paper: the weak-norming step of the proof of Theorem 3.1. The (r+1)-graph H_alpha is weakly norming; in particular, for every (r+1)-graphon W_alpha, the homomorphism density of the [r]-chain core G_alpha under the weight vector q, raised to the power C(m,r), is at most the homomorphism density of H_alpha under the same weight vector: t_{G_alpha}(W_alpha) ^ C(m,r) <= t_{H_alpha}(W_alpha). The hypergraph H_alpha decomposes into C(m,r) edge-disjoint copies of G_alpha, one for each r-subset F of [m], intersecting only in the anchor part; the weak-norming property of the reflection hypergraph G_alpha turns the product of the per-F densities into the power of the single density. The reflection-group construction behind the weak-norming property, from the authors' earlier work with Hatami's theory, is the proposed work of this milestone.
--
--   **Formalization Note** The weak-norming property itself is the external ingredient here; the decomposition and the exponent C(m,r) are visible in the two chain hypergraphs of the hypergraph layer (gAlpha as the core, hAlpha as the full chain hypergraph).
-- source:
--   D. Conlon, J. Lee, Sidorenko's conjecture for blow-ups, Discrete Anal. 2021:2 (2021), Section 3 (Lemma 3.3, page 7) and Appendix A (the weakly norming discussion).

import Mathlib
import Definitions.Def_SidB_graph
import Definitions.Def_SidB_hyper

namespace SidB

/-!  Milestone 4 (Lemma 3.3): the weak-norming bound for the chain
hypergraph. Let r be positive with r at most m and let the copy numbers
beta_k be positive. The chain hypergraph H_alpha is weakly norming, and in
particular, for every graphon, the homomorphism density of the [r]-chain
core hypergraph G_alpha raised to the power C(m,r) is at most the
homomorphism density of H_alpha, both under the weight vector q. The
hypergraph H_alpha decomposes into C(m,r) edge-disjoint copies of G_alpha,
and the weak-norming property of the reflection hypergraph G_alpha (the
content of the authors' earlier work with the reflection-group
constructions, carried in the mission as proposed work through the
Hoelder-type inequality for hypergraph functionals) yields the inequality. -/
theorem weakly_norming_bound (g : Graphon) (m r : ℕ) (β : ℕ → ℕ) (hr : 0 < r) (hmr : r ≤ m)
    (hβ : ∀ k, 1 ≤ k → k ≤ r → 0 < β k) :
    rDens g (gAlpha r β) (qOf r β) ^ (m.choose r : ℝ) ≤ rDens g (hAlpha m r β) (qOf r β) := by sorry

end SidB
