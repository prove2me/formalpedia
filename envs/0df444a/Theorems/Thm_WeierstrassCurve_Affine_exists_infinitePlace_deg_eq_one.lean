-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_exists_infinitePlace_deg_eq_one
-- name    : WeierstrassCurve.Affine.exists_infinitePlace_deg_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/5c6836b7-ec98-58a8-a353-7244ef5ac542
-- title:
--   Unique degree-one place at infinity of a Weierstrass function field
-- statement:
--   Let $F$ be a field and let $W$ be a Weierstrass curve over $F$ in affine form, with coordinate ring `W.CoordinateRing` and function field `W.FunctionField`. Here a place of `W.FunctionField` over $F$ is a valuation subring $O$ of the function field such that $O$ contains the image of $F$ under the structure map, $O \neq \top$ (that is, $O$ is not the whole function field), and $O$ is a principal ideal ring; its degree `deg` is the $F$-dimension $\operatorname{finrank}_F$ of the residue field $O/\mathfrak{m}_O$. The assertion is that there exists such a place $v_\infty$ with three properties: its degree equals $1$; it is not the case that every element $r$ of `W.CoordinateRing` has its image under the algebra map into `W.FunctionField` lying in the valuation subring of $v_\infty$ (so the affine coordinate ring is not contained in $O_{v_\infty}$); and $v_\infty$ is the only place with this last property, i.e. every place $v$ of `W.FunctionField` over $F$ whose valuation subring fails to contain the image of the whole coordinate ring is equal to $v_\infty$. No smoothness or non-singularity hypothesis on $W$ is imposed.
--
--   This is the place at infinity of a Weierstrass function field: the unique place not lying on the affine model, rational over the base field. Its three clauses form the infinite-place input to the dictionary between places and points on a genus-one curve, and it is used in establishing that divisors of degree zero on a Weierstrass curve over an algebraically closed field are principal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_exists_infinitePlace_deg_eq_one.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.Affine.exists_infinitePlace_deg_eq_one {F : Type*} [Field F] (W : WeierstrassCurve.Affine F) : ∃ vInf : AlgebraicCurve.Place F W.FunctionField, vInf.deg = 1 ∧ (¬ ∀ r : W.CoordinateRing, algebraMap W.CoordinateRing W.FunctionField r ∈ vInf.toValuationSubring) ∧ ∀ v : AlgebraicCurve.Place F W.FunctionField, (¬ ∀ r : W.CoordinateRing, algebraMap W.CoordinateRing W.FunctionField r ∈ v.toValuationSubring) → v = vInf := by sorry
