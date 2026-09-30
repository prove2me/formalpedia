-- Prove2me | Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_exists_embedded_regular
-- name    : PhilipponMultiplicity.SectionThreeSupport.exists_embedded_regular
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T02:39:03.403922+00:00
-- url     : https://prove2.me/theorems/7c65d3c7-5f9f-4be5-9896-260ad779dfd4
-- title:
--   Fact D — remove embedded components with a regular element
-- statement:
--   Let $I=\bigcap_i Q_i$ be a genuine finite minimal homogeneous primary decomposition. There is an element $x$ in the intersection of all embedded components whose image is a non-zero-divisor modulo the intersection of all isolated components. All isolated components, including irrelevant ones, are retained.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, Fact D, printed p. 369, https://www.numdam.org/articles/10.24033/bsmf.2060/. A granular supporting assertion for the original Section 3 statements; definitions are unchanged.

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.SectionThreeSupport.exists_embedded_regular
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing)
    (D : PrimaryDecomposition M I) :
    ∃ Q ∈ D.embeddedIntersection,
      IsRegular (Ideal.Quotient.mk D.isolatedIntersection Q) := by sorry
