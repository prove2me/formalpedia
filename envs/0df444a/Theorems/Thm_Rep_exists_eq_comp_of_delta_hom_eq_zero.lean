-- Prove2me | Theorems.Thm_Rep_exists_eq_comp_of_delta_hom_eq_zero
-- name    : Rep.exists_eq_comp_of_delta_hom_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/5c685248-eaab-59b3-b703-6b33b3e7986e
-- title:
--   Lifting a morphism with vanishing connecting class
-- statement:
--   Let $G$ be a group and let $R$ be an object of $\mathrm{Rep}\,\mathbb{Z}\,G$, i.e. a $\mathbb{Z}$-linear representation of $G$. Let $T$ be a short complex $T_1 \xrightarrow{f} T_2 \xrightarrow{g} T_3$ in $\mathrm{Rep}\,\mathbb{Z}\,G$, and assume that its image under the internal-hom functor $\mathrm{ihom}\,R = \underline{\mathrm{Hom}}(R,-)$ is short exact, i.e. that $0 \to \underline{\mathrm{Hom}}(R,T_1) \to \underline{\mathrm{Hom}}(R,T_2) \to \underline{\mathrm{Hom}}(R,T_3) \to 0$ is a short exact sequence of representations. Let $t : R \to T_3$ be a morphism of representations. Transport $t$ to a class in $H^0(G, \underline{\mathrm{Hom}}(R,T_3))$ by first using the isomorphism `Representation.linHom.invariantsEquivRepHom` between the $G$-invariants of $\mathrm{Hom}_{\mathbb{Z}}(R,T_3)$ and the morphisms $R \to T_3$ in $\mathrm{Rep}\,\mathbb{Z}\,G$, read backwards, and then the inverse of `groupCohomology.H0Iso`. Assume that the connecting homomorphism $\delta^{0,1}$ of the long exact cohomology sequence attached to the above short exact sequence annihilates this class. Then $t$ factors through $g$: there exists a morphism $s : R \to T_2$ of representations with $t = s$ followed by $g$.
--
--   This is exactness of the long exact $\mathrm{Ext}$-sequence at the relevant term, expressed in terms of morphisms of representations rather than cohomology classes: the kernel of the connecting map on $H^0$ is the image of post-composition with $g$. It is invoked in the construction of a nondegenerate pairing between the $H^1$- and $H^2$-type groups appearing in [`groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two`](thm.html#groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_eq_comp_of_delta_hom_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory

theorem Rep.exists_eq_comp_of_delta_hom_eq_zero {G : Type} [Group G] (R : Rep ℤ G)
    {T : ShortComplex (Rep ℤ G)} (hT : (T.map (ihom R)).ShortExact)
    (t : R ⟶ T.X₃) (ht : (groupCohomology.δ hT 0 1 rfl).hom
        ((groupCohomology.H0Iso ((ihom R).obj T.X₃)).inv ((Representation.linHom.invariantsEquivRepHom R T.X₃).symm t)) = 0) :
    ∃ s : R ⟶ T.X₂, t = s ≫ T.g := by sorry
