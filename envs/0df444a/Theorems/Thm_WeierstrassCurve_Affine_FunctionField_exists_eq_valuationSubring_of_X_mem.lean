-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_FunctionField_exists_eq_valuationSubring_of_X_mem
-- name    : WeierstrassCurve.Affine.FunctionField.exists_eq_valuationSubring_of_X_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/c94ee531-818b-58a6-a89d-826b093bfee8
-- title:
--   Valuation rings of K(W) containing x are finite places
-- statement:
--   Let $K$ be a field and $W$ a Weierstrass curve over $K$, and assume that the coordinate ring $W.\mathrm{toAffine}.\mathrm{CoordinateRing}$ of its affine model — the quotient of $K[X][Y]$ by the Weierstrass polynomial — is a Dedekind domain; write $K(W)$ for the associated function field, i.e. the fraction field of that coordinate ring. Let $O$ be a valuation subring of $K(W)$ subject to three hypotheses: $O \neq \top$, so $O$ is a proper subring of $K(W)$; every constant lies in $O$, i.e. $\mathrm{algebraMap}\,K\,K(W)\,c \in O$ for all $c \in K$; and the image in $K(W)$ of the class of $C\,X$ in the coordinate ring, that is the coordinate function $x$, lies in $O$. The conclusion is that $O$ is a finite place: there exists $v$ in the height-one spectrum of the coordinate ring, i.e. a nonzero prime ideal $\mathfrak p$ of $K[W]$, such that $O$ coincides with the valuation subring of the $\mathfrak p$-adic valuation $v.\mathrm{valuation}$ on $K(W)$. Nothing is asserted about uniqueness of $v$.
--
--   This is the affine half of the classification of the places of the function field of a Weierstrass curve over $K$: a proper valuation subring containing the constants and the coordinate function $x$ is the localisation of the affine coordinate ring at a nonzero prime, the remaining case being the place at infinity. It is used in the project's development of places of genus-one curves, for instance to identify the place attached to an affine point and in the verification that $x$ is not in the valuation subring of the place at the origin, and hence in the Abel-theorem machinery for genus-one curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_FunctionField_exists_eq_valuationSubring_of_X_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.Affine.FunctionField.exists_eq_valuationSubring_of_X_mem {K : Type*} [Field K] (W : WeierstrassCurve K) [IsDedekindDomain W.toAffine.CoordinateRing] (O : ValuationSubring W.toAffine.FunctionField) (hO : O ≠ ⊤) (hK : ∀ c : K, algebraMap K W.toAffine.FunctionField c ∈ O) (hX : algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X)) ∈ O) : ∃ v : IsDedekindDomain.HeightOneSpectrum W.toAffine.CoordinateRing, O = (v.valuation W.toAffine.FunctionField).valuationSubring := by sorry
