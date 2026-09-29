-- Prove2me | Theorems.Thm_Subalgebra_faithfullyFlat_of_directed_of_forall_faithfullyFlat
-- name    : Subalgebra.faithfullyFlat_of_directed_of_forall_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/25302adc-d86b-5c97-878c-e26f90b8a1cc
-- title:
--   Faithful flatness over a directed union of subalgebras
-- statement:
--   Let $k$ be a field, $H$ a commutative $k$-algebra, and $K$ a $k$-subalgebra of $H$. Let $(F_i)_{i \in \iota}$ be a family of $k$-subalgebras of $H$ indexed by a nonempty type $\iota$, and assume: the family is directed for inclusion, that is, for all $i, j$ there is $l$ with $F_i \le F_l$ and $F_j \le F_l$; each $F_i$ is contained in $K$; every element of $K$ lies in $F_i$ for some $i$ (so $K$ is the directed union of the $F_i$); and, for each $i$, $H$ is a faithfully flat module over $F_i$, i.e. $H$ is flat over $F_i$ and $\mathfrak{m}H \neq H$ for every maximal ideal $\mathfrak{m}$ of $F_i$. The conclusion is that $H$ is a faithfully flat module over $K$, for the $K$-module structure coming from the inclusion $K \subseteq H$. No commutativity or Noetherian hypothesis beyond $H$ being a commutative ring is imposed, and the subalgebras are not assumed finitely generated.
--
--   This is the standard passage to the limit for faithful flatness along a directed union of base rings, used to reduce questions of faithful flatness of a commutative algebra over a subalgebra to the finitely generated case. It is invoked in the proof that a commutative Hopf algebra over a field is faithfully flat over a suitable subalgebra, via [`HopfAlgebra.faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem`](thm.html#HopfAlgebra.faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subalgebra_faithfullyFlat_of_directed_of_forall_faithfullyFlat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem Subalgebra.faithfullyFlat_of_directed_of_forall_faithfullyFlat
    {k : Type u} [Field k] {H : Type v} [CommRing H] [Algebra k H] (K : Subalgebra k H)
    {ι : Type w} [Nonempty ι] (F : ι → Subalgebra k H) (hdir : Directed (· ≤ ·) F)
    (hle : ∀ i, F i ≤ K) (hcov : ∀ x ∈ K, ∃ i, x ∈ F i)
    (hff : ∀ i, Module.FaithfullyFlat ↥(F i) H) :
    Module.FaithfullyFlat ↥K H := by sorry
