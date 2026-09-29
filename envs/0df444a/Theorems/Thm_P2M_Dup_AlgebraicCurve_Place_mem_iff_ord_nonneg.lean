-- Prove2me | Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
-- name    : P2M.Dup.AlgebraicCurve.Place.mem_iff_ord_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/9df28f64-daf8-58d2-9abd-1f4ba1354da6
-- title:
--   Valuation ring membership iff non-negative order
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$ in the sense of the project notion `Place`: a valuation subring $\mathcal{O}_v$ of $F$ (recorded as `v.toValuationSubring`) which contains the image of $K$ under the structure map $K \to F$, is not all of $F$, and is a principal ideal ring. For an element $f$ of $F$ assumed non-zero, the theorem asserts the equivalence of the following two statements: $f$ lies in the valuation subring $\mathcal{O}_v$, and $0 \le v.\mathrm{ord}(f)$, where $v.\mathrm{ord}(f)$ is the integer $-\log$ of the value of $f$ under the adic valuation of $v$, i.e. $\mathrm{ord}(f) = -\log\big(v_{\mathcal{O}_v}(f)\big)$ with $v_{\mathcal{O}_v} \colon F \to \mathbb{Z}^{m0}$ the valuation attached to the height-one prime of $\mathcal{O}_v$ (`Place.adicValuation`, defined as the `HeightOneSpectrum` valuation of `v.heightOneSpectrum` on $F$) and $\log$ the `WithZero` logarithm. Thus the integer-valued order function of a place detects, by its sign, membership in the local ring of the place.
--
--   This is the standard compatibility between the valuation ring of a place of a function field and its normalised order function: $\mathcal{O}_v = \{f : \mathrm{ord}_v(f) \ge 0\}$ on non-zero elements. It is a basic tool in the project's treatment of places, divisors and the divisor class group, and is invoked throughout the development of annuli, charts and residues on curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_mem_iff_ord_nonneg.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem P2M.Dup.AlgebraicCurve.Place.mem_iff_ord_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f := by sorry
