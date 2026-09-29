-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_deg_ofHeightOneSpectrum_eq_one
-- name    : WeierstrassCurve.Affine.deg_ofHeightOneSpectrum_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/d6fc8981-f5b1-59e0-abbf-95e2ae840c17
-- title:
--   Places of a Weierstrass function field over ̄ F have degree one
-- statement:
--   Let $F$ be an algebraically closed field and let $W$ be an affine Weierstrass curve over $F$ whose coordinate ring $W.\mathrm{CoordinateRing}$ is assumed to be a Dedekind domain, and let $w$ be a height-one prime of that coordinate ring. Consider the place of the function field $W.\mathrm{FunctionField}$ over $F$ attached to $w$ by [`AlgebraicCurve.Place.ofHeightOneSpectrum`](def/AlgebraicCurve_DivisorClassGroup.html#L465), that is, the datum consisting of the valuation subring of the $w$-adic valuation on the function field, together with the verifications that it contains the image of $F$, that it is not the whole field, and that it is a principal ideal ring. The assertion is that the degree of this place is $1$, where by definition the degree of a place is the $F$-dimension $\mathrm{Module.finrank}$ of the residue field of its valuation subring, i.e. of the quotient of the valuation ring by its maximal ideal. Equivalently, the residue field of the $w$-adic place is $F$ itself.
--
--   This is the statement that over an algebraically closed base field all finite places of the function field of an affine Weierstrass curve are rational, i.e. of residue degree one; it is the degree computation needed when the divisor-theoretic formalism on Weierstrass curves is set up. It is used in the construction of principal divisors on such curves ([`WeierstrassCurve.Affine.hasPrincipalDivisors_of_isAlgClosed`](thm.html#WeierstrassCurve.Affine.hasPrincipalDivisors_of_isAlgClosed)) and in the genus-one place argument [`WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_abelTheorem`](thm.html#WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_abelTheorem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_deg_ofHeightOneSpectrum_eq_one.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.Affine.deg_ofHeightOneSpectrum_eq_one {F : Type*} [Field F] [IsAlgClosed F] (W : WeierstrassCurve.Affine F) [IsDedekindDomain W.CoordinateRing] (w : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing) : (AlgebraicCurve.Place.ofHeightOneSpectrum (K := F) (F := W.FunctionField) w).deg = 1 := by sorry
