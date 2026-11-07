-- Prove2me | Theorems.Thm_UAVariety_Mod_isVariety
-- name    : UAVariety.Mod_isVariety
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T17:46:29.240855+00:00
-- url     : https://prove2.me/theorems/71f3f3f0-69e6-440a-92d6-0eeeda2c0dc3
-- title:
--   An equational class is a variety
-- statement:
--   $L$ is a signature without relation symbols (`[L.IsAlgebraic]`); an algebra is an $L$-structure (`Alg L` bundles one). The term algebra $T(X)$ is `L.Term X` with the operations building terms; `t.realize v` is the value of the term $t$ in an algebra under the assignment $v$ of the variables. $A\models p\approx q$ (`Satisfies A (p, q)`) means $p^A(v)=q^A(v)$ for every assignment $v:X\to A$. A congruence (`Congruence M`) is an equivalence relation on $M$ compatible with the operations, and `φ.Quot` is the quotient algebra $M/\varphi$ (Mathlib's quotient structure, `Quotient.mk φ.toSetoid a` $= a/\varphi$). `Id K` is the set of identities over the variables $\mathbb N$ true in all of $K$, and `Mod E` the class of algebras satisfying all identities in $E$.
--
--   **Claim.** For every set $E$ of identities over $\mathbb N$, the class $M(E)$ of algebras satisfying $E$ is closed under homomorphic images, subalgebras and direct products, i.e. it is a variety.
-- source:
--   S. Burris, H. P. Sankappanavar, A Course in Universal Algebra, Millennium Edition (2012), https://www.math.uwaterloo.ca/~snburris/htdocs/ualg.html, Ch. II, §11, Thm 11.9 (easy direction, via Lemma 11.3)

import Definitions.Def_UAVariety_defs

universe u v w

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- B&S Thm 11.8 direction: the class `Mod E` of models of a set of identities is a variety (closed under `H`, `S`, `P`), by Lemma 11.3. -/
theorem Mod_isVariety (E : Set (L.Term ℕ × L.Term ℕ)) : IsVariety (Mod E) := by sorry

end UAVariety
