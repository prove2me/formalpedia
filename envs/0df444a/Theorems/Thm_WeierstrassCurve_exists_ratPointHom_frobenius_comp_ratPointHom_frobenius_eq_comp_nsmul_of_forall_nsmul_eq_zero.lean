-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_ratPointHom_frobenius_comp_ratPointHom_frobenius_eq_comp_nsmul_of_forall_nsmul_eq_zero
-- name    : WeierstrassCurve.exists_ratPointHom_frobenius_comp_ratPointHom_frobenius_eq_comp_nsmul_of_forall_nsmul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/af3727b6-179b-5dd5-8823-9ecc3ba7e8d0
-- title:
--   Supersingular [p] is Frobenius squared up to isomorphism
-- statement:
--   Let $\kappa$ be an algebraically closed field of characteristic a prime $p$, and let $W$ be a Weierstrass curve over $\kappa$ which is elliptic (invertible discriminant), subject to the hypothesis that the only affine point $P \in W(\kappa)$ with $p \cdot P = 0$ is $P = 0$. Write $W' = (W^{\mathrm{frob}})^{\mathrm{frob}}$ for the curve obtained by applying the $p$-power Frobenius ring homomorphism of $\kappa$ twice to the coefficients of $W$, i.e. `(W.map (frobenius κ p)).map (frobenius κ p)`. The assertion is that there exist additive homomorphisms $\varepsilon \colon W'(\kappa) \to W(\kappa)$ and $\varepsilon' \colon W(\kappa) \to W'(\kappa)$ on the groups of affine points such that: each of $\varepsilon$, $\varepsilon'$ lies in `rationalHomSet`, that is, is either the zero homomorphism or rationally represented — there are bivariate polynomials $n_X, d_X, n_Y, d_Y$ over the base and a finite set $B \subseteq \kappa$ such that at every nonsingular point $(x,y)$ with $x \notin B$ the denominators are nonzero and the homomorphism sends $(x,y)$ to $(n_X/d_X, n_Y/d_Y)$ evaluated there; $\varepsilon \circ \varepsilon' = \mathrm{id}$ and $\varepsilon' \circ \varepsilon = \mathrm{id}$; and, writing $F$ for the map on points induced by the coefficient Frobenius ($0 \mapsto 0$, $(x,y) \mapsto (x^p, y^p)$), one has $p \cdot \mathrm{id}_{W(\kappa)} = \varepsilon \circ F_{W^{\mathrm{frob}}} \circ F_W$ and $F_{W^{\mathrm{frob}}} \circ F_W = \varepsilon' \circ (p \cdot \mathrm{id}_{W(\kappa)})$.
--
--   This is the standard characterisation of supersingularity in the form: on an elliptic curve over an algebraically closed field of characteristic $p$ with no nontrivial $p$-torsion, multiplication by $p$ coincides with the square of the $p$-power Frobenius up to an isomorphism $W^{(p^2)} \cong W$ (Silverman V.3.1(a)), here recorded at the level of point groups together with rationality of the isomorphism. It is used in the analysis of the Frobenius action in the Čerednik–Drinfel'd setting, namely by [`CerednikDrinfeld.image_kernelIdealSet_ratPointHom_frobenius_comp_eq_star_smul_ofFiniteIdele_mul`](thm.html#CerednikDrinfeld.image_kernelIdealSet_ratPointHom_frobenius_comp_eq_star_smul_ofFiniteIdele_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_ratPointHom_frobenius_comp_ratPointHom_frobenius_eq_comp_nsmul_of_forall_nsmul_eq_zero.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_RatPointHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.exists_ratPointHom_frobenius_comp_ratPointHom_frobenius_eq_comp_nsmul_of_forall_nsmul_eq_zero
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (W : WeierstrassCurve κ) [W.IsElliptic] (hss : ∀ P : W.toAffine.Point, p • P = 0 → P = 0) :
    ∃ (ε : ((W.map (frobenius κ p)).map (frobenius κ p)).toAffine.Point →+ W.toAffine.Point)
      (ε' : W.toAffine.Point →+ ((W.map (frobenius κ p)).map (frobenius κ p)).toAffine.Point),
      ε ∈ WeierstrassCurve.rationalHomSet κ ((W.map (frobenius κ p)).map (frobenius κ p)) W ∧
      ε' ∈ WeierstrassCurve.rationalHomSet κ W ((W.map (frobenius κ p)).map (frobenius κ p)) ∧
      ε.comp ε' = AddMonoidHom.id _ ∧ ε'.comp ε = AddMonoidHom.id _ ∧
      (p : ℕ) • AddMonoidHom.id W.toAffine.Point =
        ε.comp ((WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W.map (frobenius κ p))).comp
          (WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W))) ∧
      (WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W.map (frobenius κ p))).comp
          (WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W)) =
        ε'.comp ((p : ℕ) • AddMonoidHom.id W.toAffine.Point) := by sorry
