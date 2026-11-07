-- Prove2me | Theorems.Thm_UAVariety_same_identities
-- name    : UAVariety.same_identities
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T14:18:00.290431+00:00
-- url     : https://prove2.me/theorems/ed27f385-905b-49ea-a35d-26f25ad991ef
-- title:
--   K, H(K), S(K), P(K) and V(K) satisfy the same identities
-- statement:
--   $L$ is a signature without relation symbols; an algebra is a type in `Type u` with an $L$-structure (`Alg L`), and $K$ is a class of algebras. $H(K)$, $S(K)$, $P(K)$ are the classes of homomorphic images, of algebras embeddable in, and of algebras isomorphic to direct products (over any index type in `Type u`, possibly empty) of members of $K$; $K$ is a variety if it is closed under $H$, $S$ and $P$. $A\models p\approx q$ means $p$ and $q$ agree under every assignment of the variables in $A$; $V(K)$ is the intersection of all varieties containing $K$. For every type $X$ of variables and terms $p,q$ over $X$: $p\approx q$ holds in every member of $H(K)$ iff it holds in every member of $K$, and likewise for $S(K)$, $P(K)$ and $V(K)$.
-- source:
--   S. Burris, H. P. Sankappanavar, A Course in Universal Algebra, Millennium Edition (2012), https://www.math.uwaterloo.ca/~snburris/htdocs/ualg.html, Ch. II, Lemma 11.3

import Definitions.Def_UAVariety_defs

universe u v w

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- B&S Lemma 11.3: `K`, `H K`, `S K`, `P K` and `V K` satisfy the same identities over any
set of variables `X` (closure under `I` is built into the operators). -/
theorem same_identities (K : Set (Alg L)) {X : Type w} (p q : L.Term X) :
    ((∀ A ∈ H K, Satisfies A (p, q)) ↔ ∀ A ∈ K, Satisfies A (p, q)) ∧
      ((∀ A ∈ S K, Satisfies A (p, q)) ↔ ∀ A ∈ K, Satisfies A (p, q)) ∧
      ((∀ A ∈ P K, Satisfies A (p, q)) ↔ ∀ A ∈ K, Satisfies A (p, q)) ∧
      ((∀ A ∈ V K, Satisfies A (p, q)) ↔ ∀ A ∈ K, Satisfies A (p, q)) := by sorry

end UAVariety
