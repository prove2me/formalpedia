-- Prove2me | Theorems.Thm_UAVariety_free_identities
-- name    : UAVariety.free_identities
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T14:18:50.539972+00:00
-- url     : https://prove2.me/theorems/e1217851-6c52-4706-94c1-c927180f2f9c
-- title:
--   Identities of K are the identities of the free algebra
-- statement:
--   $L$ is a signature without relation symbols; an algebra is a type in `Type u` with an $L$-structure (`Alg L`), and $K$ is a class of algebras. $A\models p\approx q$ means $p$ and $q$ agree under every assignment of the variables in $A$; $\mathrm{Mod}(E)$ is the class of algebras satisfying every identity in $E$ (identities over the variables $\mathbb N$), and $\mathrm{Id}(K)$ the set of identities over $\mathbb N$ true in every member of $K$. $F_K(\bar X)=T(X)/\theta_K(X)$, where $T(X)$ is the term algebra over $X$ and $\theta_K(X)$ is the intersection of all congruences $\varphi$ on $T(X)$ with $T(X)/\varphi\in S(K)$; $\bar x$ and $\bar p$ are the classes of a variable and of a term. For every type $X$ in `Type u` and terms $p,q$ over $X$: $K\models p\approx q$ iff $F_K(\bar X)\models p\approx q$, iff $\bar p=\bar q$ in $F_K(\bar X)$, iff $(p,q)\in\theta_K(X)$.
-- source:
--   S. Burris, H. P. Sankappanavar, A Course in Universal Algebra, Millennium Edition (2012), https://www.math.uwaterloo.ca/~snburris/htdocs/ualg.html, Ch. II, Theorem 11.4

import Definitions.Def_UAVariety_defs

universe u v w

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- B&S Thm 11.4: for terms `p, q` over `X`, `K ⊨ p ≈ q` iff `F_K(X̄) ⊨ p ≈ q` iff
`p̄ = q̄` in `F_K(X̄)` iff `(p, q) ∈ θ_K(X)`. -/
theorem free_identities (K : Set (Alg L)) (X : Type u) (p q : L.Term X) :
    ((∀ A ∈ K, Satisfies A (p, q)) ↔ Satisfies (freeAlg K X) (p, q)) ∧
      (Satisfies (freeAlg K X) (p, q) ↔ freeMk K X p = freeMk K X q) ∧
      (freeMk K X p = freeMk K X q ↔ (freeCong K X).r p q) := by sorry

end UAVariety
