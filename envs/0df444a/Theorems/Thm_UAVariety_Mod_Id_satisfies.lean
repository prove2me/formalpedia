-- Prove2me | Theorems.Thm_UAVariety_Mod_Id_satisfies
-- name    : UAVariety.Mod_Id_satisfies
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T17:46:22.359941+00:00
-- url     : https://prove2.me/theorems/14069586-2c87-4788-867c-823270414505
-- title:
--   Models of the ℕ-identities of K satisfy K's identities over any variable set
-- statement:
--   $L$ is a signature without relation symbols (`[L.IsAlgebraic]`); an algebra is an $L$-structure (`Alg L` bundles one). The term algebra $T(X)$ is `L.Term X` with the operations building terms; `t.realize v` is the value of the term $t$ in an algebra under the assignment $v$ of the variables. $A\models p\approx q$ (`Satisfies A (p, q)`) means $p^A(v)=q^A(v)$ for every assignment $v:X\to A$. A congruence (`Congruence M`) is an equivalence relation on $M$ compatible with the operations, and `φ.Quot` is the quotient algebra $M/\varphi$ (Mathlib's quotient structure, `Quotient.mk φ.toSetoid a` $= a/\varphi$). `Id K` is the set of identities over the variables $\mathbb N$ true in all of $K$, and `Mod E` the class of algebras satisfying all identities in $E$.
--
--   **Claim.** Let $K$ be a class of algebras, $X$ any set and $p,q\in T(X)$ with $K\models p\approx q$. If $A\models \mathrm{Id}_K(\mathbb N)$, then $A\models p\approx q$. (Rename the finitely many variables occurring in $p,q$ injectively into $\mathbb N$.)
-- source:
--   S. Burris, H. P. Sankappanavar, A Course in Universal Algebra, Millennium Edition (2012), https://www.math.uwaterloo.ca/~snburris/htdocs/ualg.html, Ch. II, §11, proof of Thm 11.9 (with Def 11.1)

import Definitions.Def_UAVariety_defs

universe u v w

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- Identities over ℕ capture identities over any set of variables: if `K ⊨ p ≈ q` for terms over an arbitrary `X`, then every model of `Id K` (identities over ℕ) satisfies `p ≈ q` (each term has finitely many variables, which can be renamed into ℕ; B&S §11, proof of Thm 11.9). -/
theorem Mod_Id_satisfies (K : Set (Alg L)) {X : Type*} (p q : L.Term X)
    (hK : ∀ B ∈ K, Satisfies B (p, q)) (A : Alg L) (hA : A ∈ Mod (Id K)) :
    Satisfies A (p, q) := by sorry

end UAVariety
