-- Prove2me | Theorems.Thm_Rep_nonempty_invariants_coind_linearEquiv_invariants
-- name    : Rep.nonempty_invariants_coind_linearEquiv_invariants
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/0f06f4c5-677b-55c9-a578-d999bd3be355
-- title:
--   Degree-zero Shapiro lemma: (CoInd_S^G N)^G ≅ N^S
-- statement:
--   Let $k$ be a commutative ring and $G$ a group (both in the same universe), let $S \le G$ be an arbitrary subgroup, and let $N$ be a $k$-linear representation of $S$, i.e. an object of `Rep k S`. Form the coinduced representation `Rep.coind S.subtype N` of $G$ along the inclusion homomorphism `S.subtype : S →* G`: its underlying $k$-module consists of the functions $\varphi \colon G \to N$ satisfying the equivariance condition $\varphi(s x) = s \cdot \varphi(x)$ for $s \in S$ and $x \in G$, with $G$ acting by right translation of the argument. The theorem asserts that the type of $k$-linear equivalences between the submodule of $G$-invariants of this coinduced representation and the submodule of $S$-invariants $N^S$ of $N$ is nonempty; that is, an isomorphism $(\mathrm{CoInd}_S^G N)^G \cong N^S$ of $k$-modules exists. Note that the statement is the bare existence assertion `Nonempty (… ≃ₗ[k] …)` rather than a named or canonical isomorphism, and that no finiteness, normality or finite-index hypothesis on $S$ is imposed.
--
--   This is the degree-zero case of Shapiro's lemma, relating the invariants of a coinduced module to the invariants of the original module over the subgroup. It is used in the proof of [`groupCohomology.euler_poincare_identity_of_hypotheses`](thm.html#groupCohomology.euler_poincare_identity_of_hypotheses).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_nonempty_invariants_coind_linearEquiv_invariants.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem Rep.nonempty_invariants_coind_linearEquiv_invariants {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) (N : Rep.{u} k S) :
    Nonempty ((Rep.coind S.subtype N).ρ.invariants ≃ₗ[k] N.ρ.invariants) := by sorry
