-- Prove2me | Theorems.Thm_WeierstrassCurve_forall_smul_eq_zero_of_mem_rationalHomSet_of_forall_smul_eq_zero
-- name    : WeierstrassCurve.forall_smul_eq_zero_of_mem_rationalHomSet_of_forall_smul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/25a98436-3c11-570f-8132-993377868046
-- title:
--   Vanishing q'-torsion transfers along a nonzero rational homomorphism
-- statement:
--   Let $\kappa$ be an algebraically closed field, let $q'$ be a prime, and assume $\kappa$ has characteristic $q'$ and is an algebra over $\mathbb{Z}/q'$ which is algebraic over it. Let $X_0$ and $W$ be Weierstrass curves over $\kappa$, each elliptic (invertible discriminant), and suppose that every point $P$ of the affine curve attached to $X_0$ with $q' \cdot P = 0$ is zero. Let $\chi$ be a homomorphism of additive groups from the points of $X_0$ base changed to $\kappa$ to the points of $W$ base changed to $\kappa$, assume $\chi \neq 0$, and assume $\chi$ lies in [`WeierstrassCurve.rationalHomSet`](def/WeierstrassCurve_RationalEnd.html#L28), i.e. $\chi$ is either zero or rationally represented: there are bivariate polynomials $nX, dX, nY, dY$ over $\kappa$ and a finite set $B \subseteq \kappa$ such that for every nonsingular point $(x,y)$ of the base changed curve with $x \notin B$ the values of $dX$ and $dY$ at $(x,y)$ are nonzero and $\chi(x,y)$ is the affine point $\bigl(nX(x,y)/dX(x,y),\, nY(x,y)/dY(x,y)\bigr)$. Then every point $P$ of the affine curve attached to $W$ with $q' \cdot P = 0$ is zero.
--
--   This is the invariance of supersingularity under a nonzero isogeny, expressed in terms of $\kappa$-points: a curve receiving a nonzero rationally represented homomorphism from a curve without nontrivial $q'$-torsion again has no nontrivial $q'$-torsion. It feeds the supersingular-point analysis in the Čerednik–Drinfeld description of the relevant modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_forall_smul_eq_zero_of_mem_rationalHomSet_of_forall_smul_eq_zero.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra CerednikDrinfeld ModularCurve

theorem WeierstrassCurve.forall_smul_eq_zero_of_mem_rationalHomSet_of_forall_smul_eq_zero
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    (X₀ : WeierstrassCurve κ) [X₀.IsElliptic] (hss : ∀ P : X₀.toAffine.Point, q' • P = 0 → P = 0)
    (W : WeierstrassCurve κ) [W.IsElliptic]
    (χ : (X₀.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point) (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W) (hχ0 : χ ≠ 0) :
    ∀ P : W.toAffine.Point, q' • P = 0 → P = 0 := by sorry
