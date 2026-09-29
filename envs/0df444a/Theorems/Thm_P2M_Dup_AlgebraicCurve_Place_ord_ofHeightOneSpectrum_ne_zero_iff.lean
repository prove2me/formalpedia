-- Prove2me | Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_ofHeightOneSpectrum_ne_zero_iff
-- name    : P2M.Dup.AlgebraicCurve.Place.ord_ofHeightOneSpectrum_ne_zero_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/f4087ed2-76b0-55fc-b089-42687d780882
-- title:
--   Order at the place of w is nonzero exactly on w
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $R$ be a commutative ring which is a Dedekind domain, equipped with an $R$-algebra structure on $F$ exhibiting $F$ as the fraction field of $R$, together with a $K$-algebra structure on $R$ compatible with the given one on $F$ (a scalar tower $K \to R \to F$). Let $w$ be a height-one prime of $R$ and let $q \in R$ be nonzero. Consider the place `Place.ofHeightOneSpectrum w` of $F$ over $K$, that is, the datum consisting of the valuation subring of the $w$-adic valuation of $F$ together with the facts that $K$ maps into it, that it is not all of $F$, and that it is a principal ideal ring. For a place $v$, the integer $v.\mathrm{ord}(f)$ is by definition $-\log$ of the value at $f$ of the $\mathbb{Z}^{m0}$-valued valuation attached to the height-one prime of the valuation subring of $v$. The assertion is that $\mathrm{ord}$ of the image of $q$ in $F$ at this place is nonzero if and only if $q$ lies in the ideal underlying $w$.
--
--   This identifies the support of the divisor of a nonzero element of a Dedekind domain inside its fraction field: the place attached to a height-one prime $w$ occurs in the divisor of $q$ precisely when $w \mid q$. It is used in the treatment of divisors on the rational function field, in the proofs that a divisor all of whose multiplicities come from a single element has degree zero and that such a divisor is principal, and in a naive height computation on the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_ofHeightOneSpectrum_ne_zero_iff.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem P2M.Dup.AlgebraicCurve.Place.ord_ofHeightOneSpectrum_ne_zero_iff {K F : Type*} [Field K] [Field F] [Algebra K F] {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
    [Algebra K R] [IsScalarTower K R F] (w : IsDedekindDomain.HeightOneSpectrum R) {q : R} (hq : q ≠ 0) :
    (Place.ofHeightOneSpectrum (K := K) (F := F) w).ord (algebraMap R F q) ≠ 0 ↔ q ∈ w.asIdeal := by sorry
