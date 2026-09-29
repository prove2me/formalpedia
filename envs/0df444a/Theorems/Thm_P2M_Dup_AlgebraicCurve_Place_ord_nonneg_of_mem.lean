-- Prove2me | Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
-- name    : P2M.Dup.AlgebraicCurve.Place.ord_nonneg_of_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/d307b413-b474-5236-96cb-fbb209d1d14d
-- title:
--   Elements of a place's valuation ring have nonnegative order
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$ in the sense of the project's structure `Place K F`: a valuation subring $\mathcal{O}_v \subseteq F$, written `v.toValuationSubring`, which contains the image of $K$ under the structure map, is not all of $F$, and whose ring structure is that of a principal ideal ring. Associated with $v$ is the valuation `v.adicValuation`, the $\mathbb{Z}^{m0}$-valued valuation on $F$ attached to the height-one prime determined by $v$, and the integer-valued order function $\mathrm{ord}_v(f) = -\log\bigl(v.\mathrm{adicValuation}(f)\bigr)$, where $\log$ is the logarithm map from $\mathbb{Z}^{m0} = \mathbb{Z} \cup \{0\}$ (multiplicatively written, with zero) to $\mathbb{Z}$. The assertion is that for every $f \in F$ lying in the valuation subring `v.toValuationSubring` one has $0 \le \mathrm{ord}_v(f)$, that is, the order of $f$ at $v$ is nonnegative.
--
--   This is the basic compatibility between membership in the local ring at a place and nonnegativity of the order of vanishing there, in the setting of places of a function field $F/K$ used to build divisors and the degree-zero divisor class group. It is invoked throughout the divisor-theoretic part of the development, for instance in the estimates relating degrees of divisors to dimensions of spaces of functions and in the analysis of annuli and of local parameters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_nonneg_of_mem.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem P2M.Dup.AlgebraicCurve.Place.ord_nonneg_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by sorry
