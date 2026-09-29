-- Prove2me | Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_isEquiv_adicValuation_ofHeightOneSpectrum
-- name    : P2M.Dup.AlgebraicCurve.Place.isEquiv_adicValuation_ofHeightOneSpectrum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/528f172d-ca7f-5f6c-81d9-ec2063b49a00
-- title:
--   The w-adic valuation is equivalent to its place's valuation
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $R$ be a Dedekind domain that is an $F$-algebra with $F$ as its fraction field, and also a $K$-algebra, the maps $K \to R \to F$ forming a scalar tower (so the inclusion $K \subseteq F$ factors through $R$). Let $w$ be a height-one prime of $R$. On the one hand there is the $w$-adic valuation `w.valuation F` on $F$, with values in $\mathbb{Z}^{m0}$. On the other hand, `Place.ofHeightOneSpectrum w` is the place of $F$ over $K$ whose underlying valuation subring is the valuation subring of `w.valuation F`: its defining data are that this subring contains $\mathrm{algebraMap}_{K,F}(a)$ for all $a \in K$, that it is not all of $F$, and that it is a principal ideal ring; and the associated `adicValuation` is the valuation on $F$ attached to the maximal ideal of that valuation subring, regarded as a height-one prime of it. The assertion is that these two valuations on $F$ are equivalent in the sense of `Valuation.IsEquiv`, i.e. they induce the same order relation $v(x) \le v(y)$ on $F$.
--
--   This identifies the normalised valuation attached to the place of a height-one prime $w$ of a Dedekind domain with the $w$-adic valuation itself, the basic compatibility needed to pass between divisors on a curve described by primes of a coordinate ring and divisors described by places of its function field. It is used in computing the degree of the place of a height-one prime of the rational function field, via [`AlgebraicCurve.RationalFunctionField.deg_ofHeightOneSpectrum`](thm.html#AlgebraicCurve.RationalFunctionField.deg_ofHeightOneSpectrum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_isEquiv_adicValuation_ofHeightOneSpectrum.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem P2M.Dup.AlgebraicCurve.Place.isEquiv_adicValuation_ofHeightOneSpectrum {K F : Type*} [Field K] [Field F] [Algebra K F] {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
    [Algebra K R] [IsScalarTower K R F] (w : IsDedekindDomain.HeightOneSpectrum R) :
    (w.valuation F).IsEquiv (Place.ofHeightOneSpectrum (K := K) w).adicValuation := by sorry
