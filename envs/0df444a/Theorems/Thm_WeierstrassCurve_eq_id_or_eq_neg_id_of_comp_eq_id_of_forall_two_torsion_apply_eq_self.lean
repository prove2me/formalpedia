-- Prove2me | Theorems.Thm_WeierstrassCurve_eq_id_or_eq_neg_id_of_comp_eq_id_of_forall_two_torsion_apply_eq_self
-- name    : WeierstrassCurve.eq_id_or_eq_neg_id_of_comp_eq_id_of_forall_two_torsion_apply_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/13ed5ba0-3f2a-5e3f-9f2d-07b13914a744
-- title:
--   Automorphism fixing the 2-torsion is ± 1
-- statement:
--   Let $F$ be a field, let $k$ be an algebraically closed field equipped with an $F$-algebra structure, and let $W$ be a Weierstrass curve over $F$ that is elliptic (invertible discriminant), and assume $2 \neq 0$ in $F$. Let $\varepsilon, \varepsilon'$ be additive endomorphisms of the group of points of the affine curve obtained from $W$ by base change to $k$, each lying in [`WeierstrassCurve.rationalHomSet k W W`](def/WeierstrassCurve_RationalEnd.html#L28), i.e. each is either the zero map or is rationally represented: there are polynomials $n_X, d_X, n_Y, d_Y \in F[X][Y]$ and a finite set $B \subseteq k$ such that for every nonsingular point $(x,y)$ of the base-changed curve with $x \notin B$ the denominators $d_X, d_Y$ evaluate to nonzero values at $(x,y)$ and the map sends $(x,y)$ to the point with coordinates $n_X(x,y)/d_X(x,y)$, $n_Y(x,y)/d_Y(x,y)$. Assume $\varepsilon' \circ \varepsilon$ and $\varepsilon \circ \varepsilon'$ are both the identity, and that $\varepsilon P = P$ for every point $P$ with $2 \cdot P = 0$. Then $\varepsilon$ is the identity endomorphism or its negative, the map $P \mapsto -P$.
--
--   This is the rigidity statement that an automorphism of an elliptic curve in characteristic different from $2$ which fixes the three nontrivial $2$-torsion points is $\pm 1$; equivalently, a curve in Legendre form with its ordered pair of marked $2$-torsion points has automorphism group $\{\pm 1\}$. It is used in the lifting argument for elliptic curves over algebraically closed fields recorded in [`WeierstrassCurve.exists_valuationSubring_residueField_equiv_and_reduceHom_comp_eq_of_isAlgClosed_of_comp_self_add_smul_eq_smul`](thm.html#WeierstrassCurve.exists_valuationSubring_residueField_equiv_and_reduceHom_comp_eq_of_isAlgClosed_of_comp_self_add_smul_eq_smul), where the normalisation by the Legendre modulus must be pinned down.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_eq_id_or_eq_neg_id_of_comp_eq_id_of_forall_two_torsion_apply_eq_self.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.eq_id_or_eq_neg_id_of_comp_eq_id_of_forall_two_torsion_apply_eq_self {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve F) [W.IsElliptic] (h2 : (2 : F) ≠ 0) {ε ε' : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point} (hε : ε ∈ WeierstrassCurve.rationalHomSet k W W) (hε' : ε' ∈ WeierstrassCurve.rationalHomSet k W W) (h₁ : ε'.comp ε = AddMonoidHom.id _) (h₂ : ε.comp ε' = AddMonoidHom.id _) (hfix : ∀ P : (W.baseChange k).toAffine.Point, (2 : ℤ) • P = 0 → ε P = P) : ε = AddMonoidHom.id _ ∨ ε = -AddMonoidHom.id _ := by sorry
