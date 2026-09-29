-- Prove2me | Theorems.Thm_TaylorWiles_tameDescentChar_comp_eq
-- name    : TaylorWiles.tameDescentChar_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/359ed33f-5a11-5686-af07-d64b64620de4
-- title:
--   Descended character satisfies ξ(π g)=χ(g)
-- statement:
--   Let $G$ and $\Delta$ be groups and $A$ a commutative ring. Given a group homomorphism $\pi \colon G \to \Delta$, a proof $h\pi$ that $\pi$ is surjective, a homomorphism $\chi \colon G \to A^\times$ into the unit group of $A$, and a hypothesis $h\chi$ that $\chi g = 1$ for every $g$ in the kernel of $\pi$, the construction [`TaylorWiles.tameDescentChar`](def/Deformations_TameDescent.html#L9) produces the homomorphism $\Delta \to A^\times$ obtained by composing the inverse of the isomorphism $\Delta \cong G/\ker\pi$ coming from surjectivity of $\pi$ with the homomorphism $G/\ker\pi \to A^\times$ induced by $\chi$ via its triviality on $\ker\pi$. The theorem asserts that for every $g \in G$ the value of this descended character at $\pi g$ equals $\chi g$; that is, the composite $\Delta \to A^\times$ precomposed with $\pi$ recovers $\chi$ pointwise.
--
--   This is the defining compatibility of the descent of a character along a surjection, i.e. the factorisation $\chi = \xi \circ \pi$ through $G/\ker\pi$ supplied by the first isomorphism theorem. In the Taylor–Wiles argument it is used when a character of an inertia group that is trivial on the kernel of the tame quotient map is rewritten as a character of the diamond group; it is cited by [`MonoidHom.exists_eq_comp_of_forall_val_sub_one_mem_maximalIdeal_of_coprime_card_ker`](thm.html#MonoidHom.exists_eq_comp_of_forall_val_sub_one_mem_maximalIdeal_of_coprime_card_ker).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TaylorWiles_tameDescentChar_comp_eq.lean

import Mathlib
import Definitions.Def_Deformations_TameDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open Function

theorem TaylorWiles.tameDescentChar_comp_eq {G : Type u} {Δ : Type v} {A : Type w} [Group G] [Group Δ] [CommRing A]
    (π : G →* Δ) (hπ : Function.Surjective π) (χ : G →* Aˣ)
    (hχ : ∀ g ∈ π.ker, χ g = 1) (g : G) :
    TaylorWiles.tameDescentChar π hπ χ hχ (π g) = χ g := by sorry
