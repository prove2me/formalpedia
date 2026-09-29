-- Prove2me | Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_adicValuation_valuationSubring
-- name    : P2M.Dup.AlgebraicCurve.Place.adicValuation_valuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/646c2de6-b8b8-518d-a699-d3d5314a5847
-- title:
--   Valuation subring of a place's adic valuation
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F/K$ in the sense of the project, i.e. the data of a valuation subring $\mathcal{O}_v = v.\mathtt{toValuationSubring}$ of $F$ such that the image of every element of $K$ under the structure map $K \to F$ lies in $\mathcal{O}_v$, such that $\mathcal{O}_v \neq F$, and such that $\mathcal{O}_v$ is a principal ideal ring (so that $\mathcal{O}_v$ is a discrete valuation ring). Attached to $v$ is the height-one prime `Place.heightOneSpectrum` of $\mathcal{O}_v$ given by its maximal ideal, and `Place.adicValuation` is the associated $\mathbb{Z}^{m0}$-valued valuation on $F$, i.e. the $\mathfrak{m}_v$-adic valuation of the Dedekind domain $\mathcal{O}_v$ extended to its fraction field $F$. The theorem asserts the equality of valuation subrings of $F$: the valuation subring $\{x \in F : v.\mathtt{adicValuation}(x) \le 1\}$ of this adic valuation is equal to $\mathcal{O}_v$ itself.
--
--   This identifies the normalised (discretely valued) valuation canonically attached to a place with the place's own valuation ring, so that the two descriptions of a place — as a valuation subring and as a $\mathbb{Z}$-valued valuation — agree. It is used in the treatment of the rational function field, where places are recognised by their valuation subrings, via [`AlgebraicCurve.RationalFunctionField.toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum`](thm.html#AlgebraicCurve.RationalFunctionField.toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_adicValuation_valuationSubring.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem P2M.Dup.AlgebraicCurve.Place.adicValuation_valuationSubring {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.adicValuation.valuationSubring = v.toValuationSubring := by sorry
