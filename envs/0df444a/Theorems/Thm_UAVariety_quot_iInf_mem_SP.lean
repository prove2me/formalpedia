-- Prove2me | Theorems.Thm_UAVariety_quot_iInf_mem_SP
-- name    : UAVariety.quot_iInf_mem_SP
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T17:14:32.933665+00:00
-- url     : https://prove2.me/theorems/d03d5b81-b21c-4bba-9af5-b6893fe4dc7a
-- title:
--   Quotient by an intersection of congruences embeds in the product of quotients
-- statement:
--   $L$ is a signature without relation symbols (`[L.IsAlgebraic]`); an algebra is an $L$-structure. The term algebra $T(X)$ is `L.Term X` with the operations building terms. A congruence (`Congruence M`) is an equivalence relation on $M$ compatible with the operations, and `φ.Quot` is the quotient algebra $M/\varphi$ (Mathlib's quotient structure). $S(K)$ is the class of algebras (in `Type u`) admitting an embedding into a member of $K$.
--
--   **Claim.** Let $(arphi_i)_{i\in I}$ be congruences on $M$ (with $I$ in the same universe) such that $M/arphi_i\in K$ for all $i$, and let $	heta=igcap_iarphi_i$. Then $a/	heta\mapsto(a/arphi_i)_{i\in I}$ is an embedding $M/	heta\hookrightarrow\prod_i M/arphi_i$, hence $M/	heta\in S(P(K))$. Here $P(K)$ is the class of algebras isomorphic to a product of members of $K$ indexed by a type in `Type u`.
-- source:
--   S. Burris, H. P. Sankappanavar, A Course in Universal Algebra, Millennium Edition (2012), https://www.math.uwaterloo.ca/~snburris/htdocs/ualg.html, Ch. II, §8 (Lemma 8.2) and the proof of Thm 10.12

import Definitions.Def_UAVariety_defs

universe u v w

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- B&S Lemma 8.2 (as used in the proof of Thm 10.12): if `θ` is the intersection of a family of congruences `φ i` with every `M/φ i ∈ K`, then `M/θ` embeds into `∏ i, M/φ i`, so `M/θ ∈ SP(K)`. -/
theorem quot_iInf_mem_SP (K : Set (Alg L)) {M : Type u} [L.Structure M] {ι : Type u}
    (φ : ι → Congruence (L := L) M) (hφ : ∀ i, Alg.of (φ i).Quot ∈ K)
    (θ : Congruence (L := L) M) (hθ : ∀ a b, θ.r a b ↔ ∀ i, (φ i).r a b) :
    Alg.of θ.Quot ∈ S (P K) := by sorry

end UAVariety
