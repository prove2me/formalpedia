-- Prove2me | Theorems.Thm_ProcNetStab_Supplement_theorem_2
-- name    : ProcNetStab.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:58:36.384059+00:00
-- url     : https://prove2.me/theorems/65f5860c-8a52-47b4-8fb8-36828a9568ff
-- title:
--   Theorem 2 (corrected: refuted, false as printed under both readings of Definition 5.1) — weighted networks and Weighted-$k$-WARPS
-- statement:
--   Theorem 2 of the paper states: a weighted network $g$ is rationalizable as weighted pairwise stable with utilities that satisfy weighted $k$-anonymity if and only if $g$ satisfies Weighted-$k$-WARPS. This item states that the claim is false under each of the two readings of weighted pairwise stability (Definition 5.1) that the paper uses. Precisely:
--
--   1. **Every weighted network is rationalizable under Definition 5.1 as printed.** For every node set $V$, type map $L : V \to T$, weighted network $g$ and $k \in \mathbb N$, $g$ is rationalizable as weighted pairwise stable (Definition 5.1, condition 2 an implication) with weighted $k$-anonymous utilities.
--   2. **Weighted-$k$-WARPS can fail.** For every $k \in \mathbb N$ there is a weighted network on four untyped nodes that violates Weighted-$k$-WARPS, for instance two disjoint links with $W_{01} = \tfrac12$ and $W_{23} = \tfrac14$.
--   3. **"If" fails under the strict reading.** There is a weighted network on five untyped nodes that satisfies Weighted-$1$-WARPS but is not rationalizable as weighted pairwise stable in the strict reading of Definition 5.1 used in Appendix A.7.1 (every increase of a weight is strictly refused by one endpoint), with weighted $1$-anonymous utilities. An example is the $0/1$-weighted network with links $\{01, 03, 24\}$.
--
--   Clauses 1 and 2 together refute the "only if" direction for every $k$ under the printed definition:
--   $$
--   \neg\bigl(\forall g,\ \text{rationalizable}(g) \Rightarrow \text{Weighted-}k\text{-WARPS}(g)\bigr).
--   $$
--   Clause 3 refutes the "if" direction under the reading on which the paper's necessity proof rests. Constant utilities satisfy the printed Definition 5.1 vacuously, so that definition imposes no restriction. In the strict reading, Weighted-$k$-WARPS ties its witnesses to a link and cannot see the non-link $12$ of the five-node example. Weighted $1$-anonymity transfers either endpoint's refusal of the link $12$ to node $0$, which would then gain by dropping one of its own links.
--
--   Differences from the source:
--
--   - correction: Theorem 2, "rationalizable as (weighted) pairwise stable with (weighted) k-anonymous preferences iff (Weighted-)k-WARPS" → its refutation: (1) under Definition 5.1 as printed every weighted network is rationalizable; (2) for every k some four-node network violates Weighted-k-WARPS, so "only if" fails; (3) under the strict reading of Definition 5.1 used in A.7.1, the five-node network with links {01, 03, 24} satisfies Weighted-1-WARPS but is not rationalizable, so "if" fails; reason: counterexamples satisfying every assumption of §5 (constant utilities for (1)–(2); for (3), each of the endpoints 1, 2 of the non-link 12 matches node 0 under ≃1 before and after a link change, so a strict refusal transfers to node 0 and contradicts condition 1 at the link 01 or 03)
--   - reading: Definition 5.1 condition 2 (printed as an implication, used in A.7.1 as "either u_i′(g) > u_i′((x, g−i′j′)) or u_j′(g) > u_j′((x, g−i′j′))" for x ∈ (W_i′j′, 1]) → both readings formalized separately, WeightedPairwiseStable (as printed) and WeightedPairwiseStableStrict (A.7.1); reason: the paper's two proofs use incompatible forms (A.7.2 the implication, A.7.1 the strict form), and the theorem fails under each
--   - reading: g − ij inside ≃k of Definition 5.2 → the weight-0 network (0, h−ij), whose unweighted network is B(h) − ij; reason: §5.1 defines ≃k for weighted networks through B(·), and (x, g−ij) at x = 0 is the network with the link ij removed
--   - reading: the networks g, g′ of Definition 5.2 → universally quantified networks h, h′, with the observed network entering only through the adjacency clause of ≃k; reason: Definition 5.2 binds g, g′, as Definition 3.9 does in the base mission
--   - reading: Definition 5.3, "for all W_ij > 0 there does not exist W_i′j′ < W_ij" → witnesses i, j with W_ij > 0 and distinct nodes i′ ≠ j′, linked or not; reason: literal text; a pair i′j′ is a pair of distinct nodes, as the non-link of Definition 4.1
--   - generalization: node set N = {1, …, n} with finitely many types (clause 1) → arbitrary node type V, type space T and type map L; reason: clause 1 holds for every node set, and the finite case is an instance
--   - encoding: weighted networks as n × n matrices with weights in [0, 1], (x, g−ij), B(g), the nodes of the counterexamples → WeightedNet with diagonal fixed at 0, setWeight writing max(0, min(x, 1)), support as a SimpleGraph, Fin 4 and Fin 5 with T = Unit, and the weights of Definition 5.2 ("for all y > x ≥ 0") taken in 0 ≤ x < y ≤ 1; reason: Lean conventions; the update agrees with the source for every weight x ∈ [0, 1], weights lie in [0, 1] by §5 (and a clipped y > 1 repeats y = 1), and the counterexamples are instances of the paper's N = {1, …, n}
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), Theorem 2, p.20; proofs Appendix A.7.1–A.7.2, pp.OA-7–OA-8 (PDF 36–37)

import Mathlib
import Definitions.Def_ProcNetStab_Supplement_WeightedRationalizable
import Definitions.Def_ProcNetStab_Supplement_WeightedRationalizableStrict
import Definitions.Def_ProcNetStab_Supplement_WeightedKWARPS

universe u

namespace ProcNetStab.Supplement

/-- **Theorem 2, refuted** (Chiong, Qi, *Stability of Procurement Networks* (authors' manuscript,
2025), Theorem 2, p.20): the printed claim "a network `g` is rationalizable as (weighted) pairwise
stable with preferences that satisfy (weighted) `k`-anonymity if and only if `g` satisfies
(Weighted-)`k`-WARPS" fails under each reading of Definition 5.1. The three clauses:

1. With Definition 5.1 as printed (condition 2 an implication), **every** weighted network, on
   every node type, with every type map and every `k`, is rationalizable (constant utilities do it).
2. For every `k` there is a weighted network on four untyped nodes that violates
   Weighted-`k`-WARPS (two disjoint links of weights `1/2` and `1/4`, a reduced form of the
   example of Figure 8, p.20). With clause 1, the "only if" direction fails for every `k` under the
   printed Definition 5.1.
3. With the strict reading of condition 2 used in Appendix A.7.1 (`WeightedPairwiseStableStrict`),
   there is a weighted network on five nodes, untyped, that satisfies Weighted-`1`-WARPS but is not
   rationalizable (the 0/1-weighted network with links `{01, 03, 24}`): the "if" direction fails.

**Formalization Note** Nodes are `Fin 4` and `Fin 5` in clauses 2 and 3, untyped (`T = Unit`).
Weighted `≃k` is the base mission's `KIso` on unweighted networks `B(·)`. -/
theorem theorem_2 :
    (∀ (V T : Type u) (L : V → T) (g : WeightedNet V) (k : ℕ), WeightedRationalizable L g k) ∧
    (∀ k : ℕ, ∃ g : WeightedNet (Fin 4), ¬ WeightedKWARPS (fun _ : Fin 4 => ()) g k) ∧
    (∃ g : WeightedNet (Fin 5), WeightedKWARPS (fun _ : Fin 5 => ()) g 1 ∧
      ¬ WeightedRationalizableStrict (fun _ : Fin 5 => ()) g 1) := by sorry

end ProcNetStab.Supplement
