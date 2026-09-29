-- Prove2me | Theorems.Thm_WeierstrassCurve_natCard_variableChange_smul_eq_subtype_eq_natCard_rationalAut_subtype
-- name    : WeierstrassCurve.natCard_variableChange_smul_eq_subtype_eq_natCard_rationalAut_subtype
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/c6c478e9-380c-59ff-856c-88159c9a5342
-- title:
--   Variable changes fixing W match invertible rational automorphisms
-- statement:
--   Let $\kappa$ be an algebraically closed field, let $W$ be a Weierstrass curve over $\kappa$ which is elliptic (invertible discriminant), and let $Q$ be an arbitrary predicate on self-maps of the set $W(\kappa)$ of affine points of `W.toAffine` (including the point at infinity). The assertion is an equality of cardinalities (`Nat.card`) of two subtypes. The first consists of those admissible variable changes $C \in$ `WeierstrassCurve.VariableChange κ` for which there is a proof $hC$ that $C \bullet W = W$ and such that $Q$ holds of the transport map $P \mapsto$ `equivOfVariableChangeEq hC P`, the bijection $W(\kappa) \to W(\kappa)$ obtained from $hC$ by transporting the variable-change equivalence `variableChangeEquiv`. The second consists of those additive maps $\iota : W(\kappa) \to W(\kappa)$ such that (i) $\iota$ lies in `rationalHomSet κ W W`, i.e. either $\iota = 0$ or $\iota$ is rationally represented: there are bivariate polynomials $nX, dX, nY, dY$ over $\kappa$ and a finite set $B \subseteq \kappa$ such that for every nonsingular point $(x,y)$ with $x \notin B$ the denominators $dX, dY$ do not vanish at $(x,y)$ and $\iota(x,y) = (nX/dX,\, nY/dY)$ evaluated there; (ii) $\iota$ has a two-sided inverse $\iota'$ (as additive maps) which again lies in `rationalHomSet κ W W`; and (iii) $Q(\iota)$ holds.
--
--   This identifies, cut by an arbitrary condition $Q$ on the induced self-map of points, the group of admissible Weierstrass variable changes preserving a fixed elliptic model with the group of invertible rational automorphisms of that model — the Weierstrass-coordinate form of the classical statement that isomorphisms of elliptic curves in Weierstrass form are admissible changes of variables. It is used in the counting of automorphisms of $\Gamma_0$-level structures on elliptic curves, via [`ModularCurve.natCard_variableChange_smul_eq_and_kernelVariableChangeDeg_eq_eq_natCard_rationalAut_map_zmultiples_eq`](thm.html#ModularCurve.natCard_variableChange_smul_eq_and_kernelVariableChangeDeg_eq_eq_natCard_rationalAut_map_zmultiples_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_natCard_variableChange_smul_eq_subtype_eq_natCard_rationalAut_subtype.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.natCard_variableChange_smul_eq_subtype_eq_natCard_rationalAut_subtype
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (W : WeierstrassCurve κ) [W.IsElliptic]
    (Q : (W.toAffine.Point → W.toAffine.Point) → Prop) :
    Nat.card {C : WeierstrassCurve.VariableChange κ //
        ∃ hC : C • W = W, Q (fun P => WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hC P)} =
      Nat.card {ι : W.toAffine.Point →+ W.toAffine.Point //
        ι ∈ WeierstrassCurve.rationalHomSet κ W W ∧
        (∃ ι' ∈ WeierstrassCurve.rationalHomSet κ W W, ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _) ∧
        Q ι} := by sorry
