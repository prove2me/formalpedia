-- Prove2me | Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_dimensionSlice_mono
-- name    : PhilipponMultiplicity.SectionThreeSupport.dimensionSlice_mono
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T02:38:54.872226+00:00
-- url     : https://prove2.me/theorems/84535cdd-d0dc-41c9-94b1-d0f11a9b0a54
-- title:
--   Fact A — monotonicity of dimension-specific primary components
-- statement:
--   Let $J\subseteq J\prime$ be multihomogeneous ideals and $b\ge0$. Write $J(b)$ for the intersection of its relevant isolated primary components of Hilbert dimension $b$, and $J(\ge b+1)$ for the corresponding intersection in larger dimensions. If $\sqrt{J(\ge b+1)}=\sqrt{J\prime(\ge b+1)}$, then $$J(b)\subseteq J\prime(b).$$ Empty intersections are the unit ideal; primary components are the actual localization–contraction ideals.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, Fact A, printed p. 365, https://www.numdam.org/articles/10.24033/bsmf.2060/. A granular supporting assertion for the original Section 3 statements; definitions are unchanged.

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.SectionThreeSupport.dimensionSlice_mono
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (J J' : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hJ' : IsMultihomogeneousIdeal M J')
    (hle : J ≤ J') (b : ℕ)
    (heq : (dimensionAtLeast M J (b + 1)).radical =
      (dimensionAtLeast M J' (b + 1)).radical) :
    dimensionSlice M J b ≤ dimensionSlice M J' b := by sorry
