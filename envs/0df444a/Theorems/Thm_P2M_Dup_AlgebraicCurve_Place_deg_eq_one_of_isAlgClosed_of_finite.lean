-- Prove2me | Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed_of_finite
-- name    : P2M.Dup.AlgebraicCurve.Place.deg_eq_one_of_isAlgClosed_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/41849e5e-04ca-5536-9d18-9cda80c6a03f
-- title:
--   Places with finite residue field over an algebraically closed base have degree one
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and suppose $K$ is algebraically closed. Let $v$ be a place of $F$ over $K$ in the sense of the project: a valuation subring $\mathcal{O}_v$ of $F$ that contains the image of $K$ under the structure map, that is not the whole of $F$, and whose ring structure is that of a principal ideal ring. Its residue field $\kappa(v)$ is the residue field of the local ring $\mathcal{O}_v$, and it carries a $K$-algebra structure; assume $\kappa(v)$ is a finite $K$-module. Then the degree of $v$, defined as $\operatorname{finrank}_K \kappa(v)$, equals $1$; equivalently, the residue field of $v$ is $K$ itself up to the canonical $K$-algebra map.
--
--   This is the standard fact that every place of finite residue degree on a function field over an algebraically closed constant field is rational, i.e. all geometric points of a curve over $\bar K$ are $K$-rational. It is used in the divisor-theoretic part of the curve package, for instance in the comparison of divisorial Weil pairings and in the statements about the index of speciality and the genus under extension of the constant field to an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed_of_finite.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem P2M.Dup.AlgebraicCurve.Place.deg_eq_one_of_isAlgClosed_of_finite
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] (v : Place K F)
    [Module.Finite K v.ResidueField] : v.deg = 1 := by sorry
