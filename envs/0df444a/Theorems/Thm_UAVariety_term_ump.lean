-- Prove2me | Theorems.Thm_UAVariety_term_ump
-- name    : UAVariety.term_ump
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T16:52:59.897623+00:00
-- url     : https://prove2.me/theorems/a2be32f8-1fd4-4f15-bbbc-4ad086c5ec0b
-- title:
--   Lemma 10.8: universal mapping property of the term algebra
-- statement:
--   $L$ is a signature without relation symbols (`[L.IsAlgebraic]`); an algebra is an $L$-structure. The term algebra $T(X)$ is `L.Term X` with the operations building terms. A congruence (`Congruence M`) is an equivalence relation on $M$ compatible with the operations, and `φ.Quot` is the quotient algebra $M/\varphi$ (Mathlib's quotient structure). $S(K)$ is the class of algebras (in `Type u`) admitting an embedding into a member of $K$.
--
--   **Claim.** For any set $X$, any algebra $A$ and any map $v:X\to A$ there is a unique homomorphism $h:T(X)\to A$ with $h(x)=v(x)$ for all $x\in X$ (namely $h(p)=p^A(v)$, term evaluation).
-- source:
--   S. Burris, H. P. Sankappanavar, A Course in Universal Algebra, Millennium Edition (2012), https://www.math.uwaterloo.ca/~snburris/htdocs/ualg.html, Ch. II, Lemma 10.8

import Definitions.Def_UAVariety_defs

universe u v w

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- B&S Lemma 10.8: the term algebra `T(X)` has the universal mapping property for every algebra: each map `X → A` extends uniquely to a homomorphism `T(X) → A` (term evaluation). -/
theorem term_ump {X : Type*} {A : Type*} [L.Structure A] (v : X → A) :
    ∃! h : L.Term X →[L] A, ∀ x, h (Term.var x) = v x := by sorry

end UAVariety
