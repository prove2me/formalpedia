-- Prove2me | Theorems.Thm_PhyloCSP_lemma_10_1
-- name    : PhyloCSP.lemma_10_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:27:58.933143+00:00
-- url     : https://prove2.me/theorems/6b7b0343-08cf-4f25-8e86-f43f52779488
-- title:
--   Lemma 10.1 — never in the middle: sampled convex orders recover $D$
-- statement:
--   Let $D$ be a random binary tree structure on $Z$ and let $<_1,<_2,\dots$ be conditionally independent uniform $D$-convex orders (Section 10.1: at each branchpoint of $D$, each order independently puts either child cone first with probability $1/2$). Then almost surely, for all distinct leaves $a,b,c$,
--   $$
--   D(a;b,c)\iff a\text{ is not between }b\text{ and }c\text{ with respect to any order }<_j , \tag{12}
--   $$
--   and in particular $D$ is a measurable function of the sequence of orders.
--
--   This lets the paper recover the random output tree from the random orders it classifies in Section 9.
--
--   Differences from the source:
--   - encoding: conditionally independent uniform D-convex orders on some probability space → the canonical model: D with law μ, independent fair coins indexed by (order index, representative pair of a branchpoint), on the product space; reason: the joint law of D and the orders is determined by μ and the sampling scheme, and both claims depend only on that joint law
--   - encoding: every realization of D is a binary tree structure → μ gives full measure to tree relations; reason: a law on H is a law concentrated on H
--   - encoding: the Fraïssé limit F = (Z, C) and its automorphism group Aut(F) → the concrete structure (Z, fraisseRel) of Definition 7.5, Z = Finset ℚ, and AutF its automorphism group; reason: Theorem 7.4 and Appendix B.1 identify the concrete structure with F, which is unique up to isomorphism; the statement is invariant under isomorphism
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Lemma 10.1 and eq. (12), p.33 (PDF p.35); sampling scheme, Section 10.1, pp.32–33

import Mathlib
import Definitions.Def_PhyloCSP_TransformationOfF
import Definitions.Def_PhyloCSP_sampledOrder
import Definitions.Def_PhyloCSP_IsConvexOrder

set_option autoImplicit false

open MeasureTheory

namespace PhyloCSP

open Classical in
/-- Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027
submission (manuscript sha256 3444b6c0…682dac), Lemma 10.1, p.33 (PDF p.35): "Let (<j)j≥1 be
conditionally independent uniform D-convex orders. Then, almost surely, for every three distinct
leaves, D(a; b, c) if and only if a is not between b and c w.r.t. any order <j. (12) In particular,
D is a measurable function of the sequence of orders." The sampling scheme is Section 10.1,
pp.32–33.

**Formalization Note.** `D` has an arbitrary law `μ` concentrated on tree relations; the orders
are `sampledOrder D c j` for independent fair coins `c` (`coinMeasure`), drawn independently of `D`:
at each branchpoint of `D` and for each `j`, an independent fair choice of which child cone comes
first. Both claims are stated: (12) almost surely for all distinct triples, and a measurable map
`Φ` from the sequence of orders (as `Bool`-valued relations, product σ-algebra) recovering `D`
almost surely. Orders are indexed from `0`. -/
theorem lemma_10_1 (μ : Measure (Z → Z → Z → Bool)) (hμ : IsTransformationOfF μ) :
    haveI : IsProbabilityMeasure μ := hμ.1
    (∀ᵐ ω ∂(μ.prod coinMeasure), ∀ a b c : Z, a ≠ b → a ≠ c → b ≠ c →
      (ω.1 a b c = true ↔ ∀ j : ℕ, ¬ Between (sampledOrder ω.1 ω.2 j) a b c)) ∧
    ∃ Φ : (ℕ → Z → Z → Bool) → (Z → Z → Z → Bool), Measurable Φ ∧
      ∀ᵐ ω ∂(μ.prod coinMeasure),
        ω.1 = Φ (fun j u v => decide (sampledOrder ω.1 ω.2 j u v)) := by sorry

end PhyloCSP
