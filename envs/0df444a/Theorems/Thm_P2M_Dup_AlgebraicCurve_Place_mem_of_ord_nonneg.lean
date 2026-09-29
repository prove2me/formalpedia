-- Prove2me | Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
-- name    : P2M.Dup.AlgebraicCurve.Place.mem_of_ord_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/ca37e605-477f-5084-ad18-3b7e34e8f02e
-- title:
--   Nonnegative order implies membership in the valuation ring
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$ in the sense of the project's structure `Place K F`: a valuation subring $v.\mathrm{toValuationSubring}$ of $F$ which contains the image of $K$ under the structure map, which is not the whole of $F$, and whose underlying ring is a principal ideal ring. Let $f \in F$ be nonzero and suppose that the integer $v.\mathrm{ord}\,f$ is nonnegative, where $v.\mathrm{ord}$ is defined as minus the logarithm (in the sense of `WithZero.log`, with values in $\mathbb{Z}$) of the value $v.\mathrm{adicValuation}\,f \in \mathbb{Z}^{m0}$, and $v.\mathrm{adicValuation}$ is the adic valuation on $F$ attached to the height-one prime `v.heightOneSpectrum` associated with the place. The conclusion is that $f$ belongs to the valuation subring $v.\mathrm{toValuationSubring}$.
--
--   This is the elementary compatibility between the integer-valued order function attached to a place and membership in its valuation ring: an element with no pole at $v$ is regular at $v$. It serves as a basic tool throughout the divisor-theoretic part of the development, being invoked in the treatment of annuli, residues and divisors on curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_mem_of_ord_nonneg.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem P2M.Dup.AlgebraicCurve.Place.mem_of_ord_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by sorry
