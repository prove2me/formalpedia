-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_variableChange_smul_eq_and_apply_some_eq_of_comp_eq_id_of_mem_rationalHomSet
-- name    : WeierstrassCurve.exists_variableChange_smul_eq_and_apply_some_eq_of_comp_eq_id_of_mem_rationalHomSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/9342fa3c-7de4-5208-bbbe-a500ee6a64ce
-- title:
--   Rational isomorphisms of elliptic curves are variable changes
-- statement:
--   Let $F$ be a field and $k$ an algebraically closed field that is an $F$-algebra, and let $W, W'$ be Weierstrass curves over $F$ which are elliptic (invertible discriminant). Let $u\colon (W_k)(k) \to (W'_k)(k)$ and $u'\colon (W'_k)(k) \to (W_k)(k)$ be homomorphisms of the groups of affine-plus-infinity points of the base-changed curves, each lying in the corresponding `rationalHomSet`, i.e. each is either zero or admits bivariate polynomials $n_X, d_X, n_Y, d_Y$ over $F$ and a finite exceptional set of abscissae in $k$ outside which, on every nonsingular point $(x,y)$, the denominators do not vanish and the map sends $(x,y)$ to $(n_X(x,y)/d_X(x,y), n_Y(x,y)/d_Y(x,y))$. Assume $u' \circ u$ and $u \circ u'$ are the respective identity homomorphisms. Then there exists a Weierstrass variable change $\gamma = (\gamma_u, \gamma_r, \gamma_s, \gamma_t)$ over $F$ with $\gamma \cdot W = W'$, together with a finite set $B \subseteq k$, such that for all $x, y \in k$ with $(x,y)$ a nonsingular point of $W_k$ and $x \notin B$, the point $u(x,y)$ is the affine point with coordinates $\gamma_u^{-2}(x - \gamma_r)$ and $\gamma_u^{-3}(y - \gamma_t - \gamma_s(x - \gamma_r))$, the images of the coefficients of $\gamma$ under $F \to k$ being understood.
--
--   This is the point-map form of the rigidity statement that an isomorphism of elliptic curves in Weierstrass form, defined over $F$ together with its inverse, is given by an admissible change of variables over $F$ (Silverman, AEC III.3.1(b)); it refines the bare existence of $\gamma$ with $\gamma \cdot W = W'$ by identifying $u$, off finitely many abscissae, with the coordinate substitution attached to $\gamma$. It is used to characterise when two rational isomorphism classes agree and in the description of the units of the rational endomorphism ring via the stabiliser of $W$ in the group of variable changes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_variableChange_smul_eq_and_apply_some_eq_of_comp_eq_id_of_mem_rationalHomSet.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_variableChange_smul_eq_and_apply_some_eq_of_comp_eq_id_of_mem_rationalHomSet {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic] (u : (W.baseChange k).toAffine.Point →+ (W'.baseChange k).toAffine.Point) (hu : u ∈ WeierstrassCurve.rationalHomSet k W W') (u' : (W'.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) (hu' : u' ∈ WeierstrassCurve.rationalHomSet k W' W) (h : u'.comp u = AddMonoidHom.id ((W.baseChange k).toAffine.Point)) (h' : u.comp u' = AddMonoidHom.id ((W'.baseChange k).toAffine.Point)) : ∃ γ : WeierstrassCurve.VariableChange F, γ • W = W' ∧ ∃ B : Set k, B.Finite ∧ ∀ (x y : k) (hxy : (W.baseChange k).toAffine.Nonsingular x y), x ∉ B → ∃ hxy', u (.some x y hxy) = .some (algebraMap F k ((γ.u⁻¹ : Fˣ) : F) ^ 2 * (x - algebraMap F k γ.r)) (algebraMap F k ((γ.u⁻¹ : Fˣ) : F) ^ 3 * (y - algebraMap F k γ.t - algebraMap F k γ.s * (x - algebraMap F k γ.r))) hxy' := by sorry
