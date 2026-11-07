-- Prove2me | Theorems.Thm_UAVariety_quot_lift_hom
-- name    : UAVariety.quot_lift_hom
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T16:52:59.562366+00:00
-- url     : https://prove2.me/theorems/b1fbadda-bfe5-4cf6-ba9d-e0186909a645
-- title:
--   Homomorphisms factor through quotients by smaller congruences
-- statement:
--   $L$ is a signature without relation symbols (`[L.IsAlgebraic]`); an algebra is an $L$-structure. The term algebra $T(X)$ is `L.Term X` with the operations building terms. A congruence (`Congruence M`) is an equivalence relation on $M$ compatible with the operations, and `φ.Quot` is the quotient algebra $M/\varphi$ (Mathlib's quotient structure). $S(K)$ is the class of algebras (in `Type u`) admitting an embedding into a member of $K$.
--
--   **Claim.** Let $\varphi$ be a congruence on $M$ and $h:M\to B$ a homomorphism with $\varphi\subseteq\ker h$. Then there is a homomorphism $g:M/\varphi\to B$ with $g(a/\varphi)=h(a)$ for all $a\in M$.
-- source:
--   S. Burris, H. P. Sankappanavar, A Course in Universal Algebra, Millennium Edition (2012), https://www.math.uwaterloo.ca/~snburris/htdocs/ualg.html, Ch. II, §6 (Thm 6.12, Thm 6.15)

import Definitions.Def_UAVariety_defs

universe u v w

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- Factorization through a quotient (B&S Ch. II §6, cf. Thm 6.12/6.15): a homomorphism whose kernel contains the congruence `φ` factors through the quotient algebra `M/φ`. -/
theorem quot_lift_hom {M : Type*} [L.Structure M] {B : Type*} [L.Structure B]
    (φ : Congruence (L := L) M) (h : M →[L] B) (hφ : ∀ a b, φ.r a b → h a = h b) :
    ∃ g : φ.Quot →[L] B, ∀ a, g (Quotient.mk _ a) = h a := by sorry

end UAVariety
