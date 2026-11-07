-- Prove2me | Theorems.Thm_UAVariety_S_S_subset_S
-- name    : UAVariety.S_S_subset_S
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T17:14:34.878143+00:00
-- url     : https://prove2.me/theorems/d06fbba4-f684-45b4-a092-1c2cb62fb3b9
-- title:
--   The subalgebra operator S is idempotent
-- statement:
--   $L$ is a signature without relation symbols (`[L.IsAlgebraic]`); an algebra is an $L$-structure. The term algebra $T(X)$ is `L.Term X` with the operations building terms. A congruence (`Congruence M`) is an equivalence relation on $M$ compatible with the operations, and `φ.Quot` is the quotient algebra $M/\varphi$ (Mathlib's quotient structure). $S(K)$ is the class of algebras (in `Type u`) admitting an embedding into a member of $K$.
--
--   **Claim.** $S(S(K))\subseteq S(K)$: if $C$ embeds into some $B$ and $B$ embeds into some $A\in K$, then $C$ embeds into $A$.
-- source:
--   S. Burris, H. P. Sankappanavar, A Course in Universal Algebra, Millennium Edition (2012), https://www.math.uwaterloo.ca/~snburris/htdocs/ualg.html, Ch. II, §9 (Lemma 9.2 and the remark that H, S, IP are idempotent)

import Definitions.Def_UAVariety_defs

universe u v w

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- B&S §9 (with Lemma 9.2): the operator `S` is idempotent, `SS = S`. A subalgebra of a subalgebra of a member of `K` is (isomorphic to) a subalgebra of that member. -/
theorem S_S_subset_S (K : Set (Alg L)) : S (S K) ⊆ S K := by sorry

end UAVariety
