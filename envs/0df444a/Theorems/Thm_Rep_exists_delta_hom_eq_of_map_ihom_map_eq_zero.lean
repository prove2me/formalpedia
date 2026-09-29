-- Prove2me | Theorems.Thm_Rep_exists_delta_hom_eq_of_map_ihom_map_eq_zero
-- name    : Rep.exists_delta_hom_eq_of_map_ihom_map_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/e4bd46d6-9146-579a-9f06-00d6a4c83d5e
-- title:
--   Classes vanishing in H¹(G,Hom(R,X₂)) are connecting images
-- statement:
--   Let $G$ be a group and let $R$ be an object of $\mathrm{Rep}\,\mathbb{Z}\,G$, i.e. a $\mathbb{Z}$-linear representation of $G$. Let $T$ be a short complex $T_1 \xrightarrow{f} T_2 \xrightarrow{g} T_3$ in $\mathrm{Rep}\,\mathbb{Z}\,G$, and assume that applying the internal hom functor $\mathrm{ihom}\,R = \operatorname{Hom}(R,-)$, with its conjugation $G$-action, to $T$ yields a short exact short complex; this is the hypothesis `hT`. Let $x$ be a class in $H^1\bigl(G,\operatorname{Hom}(R,T_1)\bigr)$ which is annihilated by the map on $H^1$ induced by the identity of $G$ and the coefficient morphism $\operatorname{Hom}(R,f)\colon \operatorname{Hom}(R,T_1)\to\operatorname{Hom}(R,T_2)$. The conclusion asserts the existence of a morphism of representations $t\colon R \to T_3$ whose associated degree-zero class maps to $x$ under the connecting homomorphism $\delta$ of the short exact sequence `hT` in degrees $0 \to 1$; here the class of $t$ is formed by transporting $t$ along the inverse of the identification of the $G$-invariants of $\operatorname{Hom}(R,T_3)$ with the equivariant maps $R \to T_3$, and then along the inverse of the isomorphism $H^0\bigl(G,\operatorname{Hom}(R,T_3)\bigr)\cong \operatorname{Hom}(R,T_3)^G$.
--
--   This is the exactness, at $H^1\bigl(G,\operatorname{Hom}(R,T_1)\bigr)$, of the long exact cohomology sequence attached to the $\operatorname{Hom}(R,-)$-transform of a short complex of representations, stated in terms of equivariant morphisms $R \to T_3$ rather than of degree-zero cohomology classes. With $R$ a relation module, $\operatorname{Hom}_G(R,N)$ and $H^1(G,\operatorname{Hom}(R,N))$ compute $\operatorname{Ext}^1$ and $\operatorname{Ext}^2$ groups, and in this form the statement feeds the construction of the pairing used in [`groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two`](thm.html#groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_delta_hom_eq_of_map_ihom_map_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory

theorem Rep.exists_delta_hom_eq_of_map_ihom_map_eq_zero {G : Type} [Group G] (R : Rep ℤ G)
    {T : ShortComplex (Rep ℤ G)} (hT : (T.map (ihom R)).ShortExact)
    (x : groupCohomology ((ihom R).obj T.X₁) 1)
    (hx : (groupCohomology.map (MonoidHom.id G) ((ihom R).map T.f) 1).hom x = 0) :
    ∃ t : R ⟶ T.X₃, (groupCohomology.δ hT 0 1 rfl).hom
        ((groupCohomology.H0Iso ((ihom R).obj T.X₃)).inv ((Representation.linHom.invariantsEquivRepHom R T.X₃).symm t)) = x := by sorry
