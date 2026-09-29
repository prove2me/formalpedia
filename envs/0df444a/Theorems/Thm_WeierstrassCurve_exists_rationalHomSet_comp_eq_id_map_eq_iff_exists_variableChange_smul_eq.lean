-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_rationalHomSet_comp_eq_id_map_eq_iff_exists_variableChange_smul_eq
-- name    : WeierstrassCurve.exists_rationalHomSet_comp_eq_id_map_eq_iff_exists_variableChange_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/ee13ba07-6cd3-519a-8011-a3b6199df0df
-- title:
--   Isomorphism of enhanced curves via rational maps or variable change
-- statement:
--   Let $\kappa$ be an algebraically closed field, $N$ a nonzero natural number, and let $E,E'$ be Weierstrass curves over $\kappa$ that are elliptic. Let $C$ be an additive subgroup of the affine point group of $E$ with $\operatorname{card} C=N$, and $C'$ an additive subgroup of that of $E'$ with $\operatorname{card} C'=N$ (the point groups of $E$ and of its base change to $\kappa$ along the identity being identified). The assertion is an equivalence. The first condition: there are additive homomorphisms $\iota$ from the points of $E$ to those of $E'$ and $\iota'$ in the opposite direction, each lying in [`WeierstrassCurve.rationalHomSet κ`](def/WeierstrassCurve_RationalEnd.html#L28), i.e. each is either zero or admits a rational representation — there exist $n_X,d_X,n_Y,d_Y \in \kappa[X][Y]$ and a finite set $B \subseteq \kappa$ such that for every nonsingular affine point $(x,y)$ with $x \notin B$ the two denominators are nonzero at $(x,y)$ and the homomorphism sends $(x,y)$ to $(n_X/d_X(x,y),\,n_Y/d_Y(x,y))$ — with $\iota' \circ \iota$ and $\iota \circ \iota'$ both the identity, and $C'$ equal to the image $\iota(C)$. The second condition: there is a Weierstrass variable change $\gamma$ over $\kappa$ with $\gamma \cdot E = E'$ such that every $T \in C$ has some $T' \in C'$ with $\mathrm{vcInvFun}\ \gamma$ applied to $T$ heterogeneously equal to $T'$, where $\mathrm{vcInvFun}$ sends $0$ to $0$ and $(x,y)$ to $(u^{-2}(x-r),\,u^{-3}(y-t-s(x-r)))$ as a point of $\gamma \cdot E$. In the second condition only the inclusion of the transported $C$ into $C'$ is required; equality is then forced by the equal cardinalities.
--
--   This is the dictionary between the two ways of expressing an isomorphism of enhanced elliptic curves $(E,C) \cong (E',C')$ over an algebraically closed field: as a pair of mutually inverse $\kappa$-rational homomorphisms carrying $C$ onto $C'$, and as an admissible change of Weierstrass coordinates $(x,y) \mapsto (u^2x+r,\,u^3y+su^2x+t)$ transporting the level structure, the form in which $\Gamma_0(N)$-level moduli points are defined. It is used in the construction and analysis of moduli places on modular curves, including the Čerednik–Drinfel'd comparison and the computation of place widths.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_rationalHomSet_comp_eq_id_map_eq_iff_exists_variableChange_smul_eq.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_ModularCurve_ModuliPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.exists_rationalHomSet_comp_eq_id_map_eq_iff_exists_variableChange_smul_eq
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ] (N : ℕ) [NeZero N]
    (E E' : WeierstrassCurve κ) [E.IsElliptic] [E'.IsElliptic]
    (C : AddSubgroup E.toAffine.Point) (hC : Nat.card C = N)
    (C' : AddSubgroup E'.toAffine.Point) (hC' : Nat.card C' = N) :
    (∃ ι ∈ WeierstrassCurve.rationalHomSet κ E E', ∃ ι' ∈ WeierstrassCurve.rationalHomSet κ E' E,
        ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _ ∧ C' = C.map ι) ↔
      ∃ γ : WeierstrassCurve.VariableChange κ, γ • E = E' ∧
        ∀ T ∈ C, ∃ T' ∈ C', HEq (WeierstrassCurve.Affine.Point.vcInvFun γ E.toAffine T) T' := by sorry
