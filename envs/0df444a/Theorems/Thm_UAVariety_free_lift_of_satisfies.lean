-- Prove2me | Theorems.Thm_UAVariety_free_lift_of_satisfies
-- name    : UAVariety.free_lift_of_satisfies
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T17:46:25.51853+00:00
-- url     : https://prove2.me/theorems/9c447507-9a99-4d68-9fdf-eddbee3b4f55
-- title:
--   F_K(X) maps onto any algebra satisfying K's identities over X
-- statement:
--   $L$ is a signature without relation symbols (`[L.IsAlgebraic]`); an algebra is an $L$-structure (`Alg L` bundles one). The term algebra $T(X)$ is `L.Term X` with the operations building terms; `t.realize v` is the value of the term $t$ in an algebra under the assignment $v$ of the variables. $A\models p\approx q$ (`Satisfies A (p, q)`) means $p^A(v)=q^A(v)$ for every assignment $v:X\to A$. A congruence (`Congruence M`) is an equivalence relation on $M$ compatible with the operations, and `φ.Quot` is the quotient algebra $M/\varphi$ (Mathlib's quotient structure, `Quotient.mk φ.toSetoid a` $= a/\varphi$). `Id K` is the set of identities over the variables $\mathbb N$ true in all of $K$, and `Mod E` the class of algebras satisfying all identities in $E$.
--
--   **Claim.** Let $A$ be an algebra such that $A\models p\approx q$ whenever $p,q\in T(X)$ and $K\models p\approx q$. Then every map $v:X\to A$ extends to a homomorphism $f:F_K(\bar X)\to A$ with $f(\bar x)=v(x)$.
-- source:
--   S. Burris, H. P. Sankappanavar, A Course in Universal Algebra, Millennium Edition (2012), https://www.math.uwaterloo.ca/~snburris/htdocs/ualg.html, Ch. II, §11, proof of Thm 11.9 (with Thms 10.10, 11.4)

import Definitions.Def_UAVariety_defs

universe u v w

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- The free algebra `F_K(X̄)` has the mapping property for every algebra `A` satisfying all identities of `K` over `X`: each map `X → A` extends to a homomorphism `F_K(X̄) → A` (B&S proof of Thm 11.9). -/
theorem free_lift_of_satisfies (K : Set (Alg L)) (X : Type u) (A : Alg L) (v : X → A)
    (hA : ∀ p q : L.Term X, (∀ B ∈ K, Satisfies B (p, q)) → Satisfies A (p, q)) :
    ∃ f : freeAlg K X →[L] A, ∀ x, f (freeGen K X x) = v x := by sorry

end UAVariety
