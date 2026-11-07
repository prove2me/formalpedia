-- Prove2me | Theorems.Thm_UAVariety_satisfies_iff_hom
-- name    : UAVariety.satisfies_iff_hom
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T17:30:18.068537+00:00
-- url     : https://prove2.me/theorems/9d506c2d-487d-4223-ada0-0bc5bac1f070
-- title:
--   An identity holds in A iff every homomorphism from the term algebra identifies its sides
-- statement:
--   $L$ is a signature without relation symbols (`[L.IsAlgebraic]`); an algebra is an $L$-structure (`Alg L` bundles one). The term algebra $T(X)$ is `L.Term X` with the operations building terms; `t.realize v` is the value of the term $t$ in an algebra under the assignment $v$ of the variables. $A\models p\approx q$ (`Satisfies A (p, q)`) means $p^A(v)=q^A(v)$ for every assignment $v:X\to A$. A congruence (`Congruence M`) is an equivalence relation on $M$ compatible with the operations, and `φ.Quot` is the quotient algebra $M/\varphi$ (Mathlib's quotient structure, `Quotient.mk φ.toSetoid a` $= a/\varphi$).
--
--   **Claim.** For an algebra $A$ and terms $p,q\in T(X)$: $A\models p\approx q$ if and only if $\alpha(p)=\alpha(q)$ for every homomorphism $\alpha:T(X)\to A$.
-- source:
--   S. Burris, H. P. Sankappanavar, A Course in Universal Algebra, Millennium Edition (2012), https://www.math.uwaterloo.ca/~snburris/htdocs/ualg.html, Ch. II, §11, Lemma 11.2 (with Def 11.1 and Lemma 10.8)

import Definitions.Def_UAVariety_defs

universe u v w

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- B&S Lemma 11.2 (one form): `A ⊨ p ≈ q` iff every homomorphism `T(X) → A` identifies `p` and `q`. -/
theorem satisfies_iff_hom {X : Type*} (A : Alg L) (p q : L.Term X) :
    Satisfies A (p, q) ↔ ∀ h : L.Term X →[L] A, h p = h q := by sorry

end UAVariety
