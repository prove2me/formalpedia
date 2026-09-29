-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_variableChange_of_comp_eq_id_of_mem_rationalHomSet
-- name    : WeierstrassCurve.exists_variableChange_of_comp_eq_id_of_mem_rationalHomSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/2842f94c-d905-5fc1-b390-6911aa022e31
-- title:
--   Mutually inverse rational maps give an F-variable change
-- statement:
--   Let $F$ be a field and $k$ an algebraically closed field extension of $F$ (with decidable equality), and let $W$, $W'$ be Weierstrass curves over $F$, both assumed elliptic. Suppose given additive maps $u\colon (W_k)(k)\to (W'_k)(k)$ and $u'\colon (W'_k)(k)\to (W_k)(k)$ between the groups of affine points of the base changes to $k$, each lying in the corresponding `rationalHomSet`: that is, each of $u$, $u'$ either is the zero homomorphism or is rationally represented over $F$, meaning there are bivariate polynomials $n_X,d_X,n_Y,d_Y$ over $F$ and a finite set $B\subseteq k$ such that for every nonsingular point $(x,y)$ of the base-changed curve with $x\notin B$ the denominators $d_X,d_Y$ do not vanish at $(x,y)$ and the map sends $(x,y)$ to the affine point with coordinates $\bigl(n_X(x,y)/d_X(x,y),\,n_Y(x,y)/d_Y(x,y)\bigr)$. Suppose further that $u$ and $u'$ are mutually inverse, i.e. $u'\circ u$ is the identity on $(W_k)(k)$ and $u\circ u'$ is the identity on $(W'_k)(k)$. The conclusion is that there exists an admissible change of Weierstrass coordinates $\gamma$ defined over $F$, i.e. $\gamma \in$ `WeierstrassCurve.VariableChange F`, with $\gamma \bullet W = W'$.
--
--   This is the Weierstrass-model form of the classical fact that an isomorphism of elliptic curves preserving the origin is induced by an admissible linear change of coordinates $x = \mu^2 x' + r$, $y = \mu^3 y' + \mu^2 s x' + t$ over the base field (Silverman, AEC III.3.1(b)), here phrased for homomorphisms of $k$-points that admit an $F$-rational description away from finitely many abscissae. It is used in the Cerednik–Drinfeld and modular-curve parts of the development, where isomorphism classes of elliptic curves are identified via such mutually inverse rational homomorphisms; the proof invokes the extraction of a polynomial representation for an injective rationally represented homomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_variableChange_of_comp_eq_id_of_mem_rationalHomSet.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_variableChange_of_comp_eq_id_of_mem_rationalHomSet {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic] (u : (W.baseChange k).toAffine.Point →+ (W'.baseChange k).toAffine.Point) (hu : u ∈ WeierstrassCurve.rationalHomSet k W W') (u' : (W'.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) (hu' : u' ∈ WeierstrassCurve.rationalHomSet k W' W) (h : u'.comp u = AddMonoidHom.id ((W.baseChange k).toAffine.Point)) (h' : u.comp u' = AddMonoidHom.id ((W'.baseChange k).toAffine.Point)) : ∃ γ : WeierstrassCurve.VariableChange F, γ • W = W' := by sorry
