-- Prove2me | Theorems.Thm_PSDPolyApprox_theorem_4
-- name    : PSDPolyApprox.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:50:45.341546+00:00
-- url     : https://prove2.me/theorems/68fc09e9-fdd6-43ea-8c0d-f15db69b5c8b
-- title:
--   Theorem 4 (corrected: ambient dimension ≥ 1) — generalized Yannakakis: min xc of a polytope between $K$ and $L$ equals $\operatorname{rank}_+ S_{K,L}$
-- statement:
--   **Theorem 4 (Generalized Yannakakis theorem).** Let $K\subseteq L\subseteq\mathbb R^d$, $d\ge1$, be convex bodies (compact convex sets) with the origin in the interior of $K$, and let $S_{K,L}$ be the slack matrix of the pair $(K,L)$: $S_{K,L}(x,y)=1-\langle x,y\rangle$ for $x$ an extreme point of $K$ and $y$ an extreme point of $L^\circ$. Then the smallest extension complexity of a polytope $P$ with $K\subseteq P\subseteq L$ equals the nonnegative rank of $S_{K,L}$:
--   $$
--   \min\{\operatorname{xc}(P): P\text{ polytope},\ K\subseteq P\subseteq L\}=\operatorname{rank}_+(S_{K,L}),
--   $$
--   both sides read in $\mathbb N\cup\{\infty\}$. Equivalently, for every $r\in\mathbb N$: some polytope $P$ with $K\subseteq P\subseteq L$ has $\operatorname{xc}(P)\le r$ if and only if $S_{K,L}$ is a sum of at most $r$ entrywise nonnegative rank-one matrices.
--
--   The case $K=L$ is Yannakakis' theorem; the general case connects polyhedral approximation of a convex body with nonnegative factorizations of an infinite matrix, which is how Theorem 1 is proved.
--
--   **Formalization Note** $\mathbb R^d$ is $\mathbb R^\iota$ for a nonempty finite type $\iota$ with the dot product and its usual topology. Nonempty interior of $K$ and $L$ follows from $0\in\operatorname{int}K\subseteq L$. A factorization of size $r'$ is $S=TU$ with $T\ge0$ having $r'$ columns and $U\ge0$ having $r'$ rows.
--
--   Differences from the source:
--   - correction: K ⊂ L ⊂ ℝ^d for any d → ℝ^ι with ι nonempty (d ≥ 1); reason: in ℝ⁰, K = L = {0} has 0 in its interior, xc({0}) = 0, but S_{K,L} is the 1 × 1 matrix (1), of nonnegative rank 1
--   - encoding: the smallest extension complexity equals the nonnegative rank → for every r: (∃ polytope P, K ⊆ P ⊆ L, xc(P) ≤ r) ↔ (∃ r' ≤ r, S_{K,L} has a nonnegative factorization of size r'); reason: equality of two minima in ℕ ∪ {∞} is the agreement of their sublevel sets; this form also covers the case where both are infinite
--   - encoding: convex body → compact convex set (nonempty interior implied by 0 ∈ interior K and K ⊆ L); reason: same instances
--   - encoding: extension complexity = smallest number of facets of a polytope whose linear image is P (Definition 1) → smallest number of inequalities of an extended formulation of P (ExtensionComplexity.TSP.extensionComplexity); reason: the two minima coincide for polytopes of dimension ≥ 1 (Fiorini et al., J. ACM 2015, Theorem 3, published as ExtensionComplexity.TSP.yannakakis_factorization), and every polytope in this statement has dimension ≥ 1
-- source:
--   Fawzi, On polyhedral approximations of the positive semidefinite cone, arXiv:1811.09649v1, Theorem 4, p.4 (citing [Yan91] and [Pas12, Section 4.1]); slack matrix: equation (2), p.4

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_Polytope
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_ExtensionComplexity_TSP_SlackMatrix
import Definitions.Def_PSDPolyApprox_pairSlackMatrix

open ExtensionComplexity.TSP

namespace PSDPolyApprox

/-- **Theorem 4 (Generalized Yannakakis theorem).**
Fawzi, arXiv:1811.09649v1, Theorem 4, p.4 (due to [Yan91] for K = L; general case [Pas12, §4.1]):
"Let K ⊂ L be two convex bodies and assume that the origin lies in the interior of K. Let SK,L be
the slack matrix of the pair (K, L) as deﬁned in Equation (2). The smallest extension complexity
of a polytope P that satisﬁes K ⊂ P ⊂ L is equal to the nonnegative rank of SK,L."

Stated as equality of the two minima in `ℕ ∪ {∞}`: for every `r`, some polytope between `K` and
`L` has extension complexity `≤ r` iff `S_{K,L}` has a nonnegative factorization of size `≤ r`
(so "no polytope in between" iff "no finite factorization").

**Formalization Note.** A convex body is compact and convex; its nonempty interior follows from
`0 ∈ interior K` and `K ⊆ L`. Extension complexity is the minimum number of inequalities of an
extended formulation (`ExtensionComplexity.TSP.extensionComplexity`), which equals the facet count
of Definition 1 for polytopes of dimension `≥ 1` (Fiorini et al., Theorem 3; every polytope
containing `K` has full dimension). `[Nonempty ι]` excludes `ℝ⁰`, where `K = L = {0}` gives
`xc({0}) = 0` but `rank₊ S = 1`. -/
theorem theorem_4 {ι : Type*} [Fintype ι] [Nonempty ι] (K L : Set (ι → ℝ))
    (hKc : IsCompact K) (hKconv : Convex ℝ K) (hLc : IsCompact L) (hLconv : Convex ℝ L)
    (h0 : (0 : ι → ℝ) ∈ interior K) (hKL : K ⊆ L) (r : ℕ) :
    (∃ P : Set (ι → ℝ), IsPolytope P ∧ K ⊆ P ∧ P ⊆ L ∧ extensionComplexity P ≤ r) ↔
      (∃ r' ≤ r, HasNonnegFactorization (pairSlackMatrix K L) r') := by sorry

end PSDPolyApprox
