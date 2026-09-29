-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_map_residue_eq_and_reduceHom_comp_eq_of_variableChange_smul_eq
-- name    : WeierstrassCurve.exists_map_residue_eq_and_reduceHom_comp_eq_of_variableChange_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/d1f5f8c1-7ca4-5df7-842a-c1a12b5a0315
-- title:
--   Lifting a variable change of the reduced model
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring, with residue map $\mathrm{res}_A : A \to \kappa := \mathrm{ResidueField}(A)$ and inclusion $A \hookrightarrow L$. Let $E'$ be a Weierstrass curve with coefficients in $A$ whose coefficientwise reduction $E' \bmod \mathfrak m_A$ over $\kappa$ has discriminant $\Delta \neq 0$ (hypothesis $h\Delta'$), let $V$ be a Weierstrass curve over $\kappa$, and let $v$ be a variable change over $\kappa$ with $v \cdot (E' \bmod \mathfrak m_A) = V$. Then there exist a Weierstrass curve $E$ over $A$, a proof that $E \bmod \mathfrak m_A$ has nonzero discriminant, and an equality $h_{\mathrm{red}} : E \bmod \mathfrak m_A = V$, together with additive maps $\theta : (E'\!\otimes\! L)(L) \to (E\!\otimes\! L)(L)$ and $\theta'$ in the opposite direction, each lying in [`WeierstrassCurve.rationalHomSet L`](def/WeierstrassCurve_RationalEnd.html#L28) (that is, each is either $0$ or is given, at all affine nonsingular points whose abscissa avoids some fixed finite set, by a single quadruple of bivariate polynomials over $L$ via $(x,y) \mapsto (n_X/d_X, n_Y/d_Y)(x,y)$ with nonvanishing denominators), such that $\theta' \circ \theta$ and $\theta \circ \theta'$ are the identity, and such that for every point $P$ of $E'$ over $L$ the reduction of $\theta(P)$, transported along $h_{\mathrm{red}}$ to $V(\kappa)$, equals the image of the reduction of $P$ under the bijection $V(\kappa) \simeq (E' \bmod \mathfrak m_A)(\kappa)$ attached to $v$, read in the inverse direction. Here reduction of points is the homomorphism sending $0$ to $0$ and an affine point $(x,y)$ to the coordinatewise residue of $(x,y)$ when $x \in A$, and to $0$ otherwise.
--
--   This is the rigidification step for models with good reduction: an isomorphism of the special fibre with a prescribed Weierstrass equation $V$ over the residue field is realised by replacing $E'$ with an $L$-isomorphic integral model $E$ reducing to $V$ exactly, the isomorphism being rational in both directions and compatible with reduction of points. It is used in the construction of nonzero rational homomorphisms between Weierstrass curves, in [`WeierstrassCurve.exists_ne_zero_mem_rationalHomSet_of_forall_nsmul_char_eq_zero`](thm.html#WeierstrassCurve.exists_ne_zero_mem_rationalHomSet_of_forall_nsmul_char_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_map_residue_eq_and_reduceHom_comp_eq_of_variableChange_smul_eq.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_PointAddEquivOfEq
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_map_residue_eq_and_reduceHom_comp_eq_of_variableChange_smul_eq {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L} [DecidableEq (IsLocalRing.ResidueField A)] (E' : WeierstrassCurve A) (hΔ' : (E'.map (IsLocalRing.residue A)).Δ ≠ 0) {V : WeierstrassCurve (IsLocalRing.ResidueField A)} (v : WeierstrassCurve.VariableChange (IsLocalRing.ResidueField A)) (hv : v • E'.map (IsLocalRing.residue A) = V) : ∃ (E : WeierstrassCurve A) (hΔ : (E.map (IsLocalRing.residue A)).Δ ≠ 0) (hred : E.map (IsLocalRing.residue A) = V), ∃ θ ∈ WeierstrassCurve.rationalHomSet L (E'.map A.subtype) (E.map A.subtype), ∃ θ' ∈ WeierstrassCurve.rationalHomSet L (E.map A.subtype) (E'.map A.subtype), θ'.comp θ = AddMonoidHom.id _ ∧ θ.comp θ' = AddMonoidHom.id _ ∧ ∀ P : (E'.map A.subtype).toAffine.Point, WeierstrassCurve.pointAddEquivOfEq hred (WeierstrassCurve.reduceHom hΔ (θ P)) = (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv).symm (WeierstrassCurve.reduceHom hΔ' P) := by sorry
