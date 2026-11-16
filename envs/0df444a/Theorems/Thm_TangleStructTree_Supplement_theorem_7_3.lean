-- Prove2me | Theorems.Thm_TangleStructTree_Supplement_theorem_7_3
-- name    : TangleStructTree.Supplement.theorem_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:14:57.086197+00:00
-- url     : https://prove2.me/theorems/dddcb000-5444-4ab8-9f06-c10ae5aa7367
-- title:
--   Theorem 7.3 — a regular profile or a $\mathcal P_s$-tree, exactly one
-- statement:
--   Let $\vec S$ be a submodular separation system in a distributive universe $U$ of separations, and put
--   $$\mathcal P_s=\big\{\{\vec r,\vec s,\overleftarrow t\}:\ \vec r,\vec s,\vec t\in U,\ \overleftarrow t\le\overleftarrow r\vee\overleftarrow s\big\}.$$
--   Then exactly one of the following holds:
--
--   1. there exists a regular profile of $S$;
--   2. there exists a $\mathcal P_s$-tree of $\vec S$.
--
--   In the case of (2), for every order function on $S$, the $\mathcal P_s$-tree can be chosen to be irreducible, efficient and ordered with respect to it.
--
--   This is a tangle-tree duality theorem for profiles, for which no such dichotomy was known from the theory of $\mathcal F$-tangles with $\mathcal F$ consisting of stars.
--
--   Differences from the source:
--   - encoding: a separation tree is a finite rooted tree with an edge labelling β → a SepTree: the finite prefix-closed set of root-path label lists; reason: the child labels of a node are distinct, so the label-list set determines the rooted labelled tree up to root- and label-preserving isomorphism and every finite separation tree arises
--   - encoding: exactly one of (i), (ii) holds; in the case of (ii) the tree can be chosen with further properties → (i) ↔ ¬ (ii), and (ii) → ∃ one tree with all the properties together; reason: "exactly one" is (i) or (ii) but not both; the chosen tree is a single tree
--   - encoding: a distributive universe of separations U and S⃗ ⊆ U → a type U with DistribLattice and SepSystem (one order), and S⃗ a SubSepSystem U (a subset closed under ∗); reason: a universe is a separation system that is a lattice in its own order
--   - encoding: P and P_s as sets of triples from U → profileFamily S and strongFamily S on S⃗: the σ ⊆ S⃗ whose image in U is such a triple; reason: triples that are not subsets of S⃗ never matter for orientations of S
--   - encoding: "with respect to any order function on S" → ∀ ord on S⃗ with IsOrderFunction ord, (ii) → ∃ a P_s-tree that is irreducible, efficient and ordered for ord; reason: efficient and ordered are relative to an order function; the tree may depend on it, as in the paper
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), Theorem 7.3, p.23 (PDF 34); = extended abstract Theorem 7.2, p.10; P and P_s, p.22 (PDF 33)

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsTangle
import Definitions.Def_TangleStructTree_IsOrderFunction
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_SepTree_IsTST
import Definitions.Def_TangleStructTree_Supplement_SubSepSystem
import Definitions.Def_TangleStructTree_Supplement_Profiles
import Definitions.Def_TangleStructTree_Supplement_IsFTree
import Definitions.Def_TangleStructTree_Supplement_IsEfficientTree
import Definitions.Def_TangleStructTree_Supplement_IsIrreducible
import Definitions.Def_TangleStructTree_Supplement_IsOrderedTree

namespace TangleStructTree

namespace Supplement

/-- **Theorem 7.3** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version (Part I), p.23 (PDF 34); = extended abstract Theorem 7.2, p.10). Let `S⃗` be any
submodular separation system in a distributive universe of separations. Then exactly one of the
following assertions holds:
(i) there exists a regular profile of `S`;
(ii) there exists a `P_s`-tree of `S⃗`.
In the case of (ii), the `P_s`-tree can be chosen to be irreducible, efficient, and ordered with
respect to any order function on `S`.

**Formalization Note**
1. The universe `U` is a distributive lattice that is a separation system, with one order (the
   lattice's); `S⃗` is a `SubSepSystem U` (a subset closed under `∗`, induced order and involution).
2. A profile of `S` is a `P`-tangle, `P = {{r⃗, s⃗, r⃖ ∨ s⃖} : r⃗, s⃗ ∈ U}` (`profileFamily S`), and it
   is regular if none of its elements `s⃗` is small (`s⃗ ≤ s⃖`; `NoSmall`). `P_s` is
   `strongFamily S`. Both families are read on `S⃗`: only their elements that are subsets of `S⃗`
   matter for orientations of `S`.
3. No finiteness is assumed (none is printed). "Exactly one" is `(i) ↔ ¬ (ii)`. "With respect to
   any order function" is: for every order function `ord` on `S`, if (ii) holds then some `P_s`-tree
   is irreducible, efficient and ordered for `ord`. -/
theorem theorem_7_3 {U : Type*} [DistribLattice U] [SepSystem U] (S : SubSepSystem U)
    (hS : IsSubmodular S) :
    ((∃ τ : Set S.Carrier, IsTangle (profileFamily S) τ ∧ NoSmall τ) ↔
        ¬ ∃ T : SepTree S.Carrier, IsFTree T (strongFamily S)) ∧
      ∀ ord : S.Carrier → ℝ, IsOrderFunction ord →
        (∃ T : SepTree S.Carrier, IsFTree T (strongFamily S)) →
        ∃ T : SepTree S.Carrier, IsFTree T (strongFamily S) ∧ IsIrreducible T (strongFamily S) ∧
          IsEfficientTree T ord ∧ IsOrderedTree T ord := by sorry

end Supplement

end TangleStructTree
