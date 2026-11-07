-- Prove2me | Theorems.Thm_UAVariety_ker_quot_mem_S
-- name    : UAVariety.ker_quot_mem_S
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T16:53:03.453761+00:00
-- url     : https://prove2.me/theorems/85494b55-70c9-418c-824d-ddbe9f7b3c4c
-- title:
--   Quotient by a kernel into a member of K lies in S(K)
-- statement:
--   $L$ is a signature without relation symbols (`[L.IsAlgebraic]`); an algebra is an $L$-structure. The term algebra $T(X)$ is `L.Term X` with the operations building terms. A congruence (`Congruence M`) is an equivalence relation on $M$ compatible with the operations, and `φ.Quot` is the quotient algebra $M/\varphi$ (Mathlib's quotient structure). $S(K)$ is the class of algebras (in `Type u`) admitting an embedding into a member of $K$.
--
--   **Claim.** If $A\in K$ and $h:M\to A$ is a homomorphism, then $\ker h=\{(a,b): h(a)=h(b)\}$ is a congruence on $M$ and $M/\ker h\in S(K)$, since $a/\ker h\mapsto h(a)$ embeds it into $A$.
-- source:
--   S. Burris, H. P. Sankappanavar, A Course in Universal Algebra, Millennium Edition (2012), https://www.math.uwaterloo.ca/~snburris/htdocs/ualg.html, Ch. II, Thm 6.12 and the proof of Thm 10.10

import Definitions.Def_UAVariety_defs

universe u v w

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- The kernel of a homomorphism into a member of `K` is a congruence whose quotient lies in `S K` (B&S Thm 6.12: `M/ker h ≅ h(M) ≤ A`; used in the proof of Thm 10.10). -/
theorem ker_quot_mem_S (K : Set (Alg L)) {M : Type u} [L.Structure M] {A : Alg L}
    (hA : A ∈ K) (h : M →[L] A) :
    ∃ φ : Congruence (L := L) M, (∀ a b, φ.r a b ↔ h a = h b) ∧ Alg.of φ.Quot ∈ S K := by sorry

end UAVariety
