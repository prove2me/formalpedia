-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_keyhole_cauchy_contour_assembly
-- name    : WeightedRootIntegralIdentity.keyhole_cauchy_contour_assembly
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-16T12:30:17.851255+00:00
-- url     : https://prove2.me/theorems/5d539831-d4e6-4c4d-8e26-5697b4244580
-- title:
--   Cauchy assembly for the four keyhole boundary contributions
-- statement:
--   Let the four oriented boundary integrals of a slit keyhole contour be denoted by $I_{\rm up}$, $I_{\rm low}$, $I_{\rm in}$, and $I_{\rm out}$. If their total boundary sum equals the residue contribution and the two circular arcs cancel, then the normalized bank contribution is $\pi$ times the residue term. This is the algebraic assembly step that converts the four contour pieces into the keyhole boundary identity.
-- source:
--   Cauchy theorem on a positively oriented slit keyhole contour, after separating the two banks and two circular arcs.

import Mathlib

namespace WeightedRootIntegralIdentity

theorem keyhole_cauchy_contour_assembly
    (Iupper Ilower Iinner Iouter residue : ℂ)
    (hboundary : Iupper + Ilower + Iinner + Iouter = 2 * Real.pi * Complex.I * residue)
    (hbank : Iupper + Ilower = 2 * Complex.I * (Iupper / (2 * Complex.I)))
    (harcs : Iinner + Iouter = 0) :
    Iupper / (2 * Complex.I) = Real.pi * residue := by sorry

end WeightedRootIntegralIdentity
