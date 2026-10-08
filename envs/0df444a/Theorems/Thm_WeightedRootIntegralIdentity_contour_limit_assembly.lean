-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_contour_limit_assembly
-- name    : WeightedRootIntegralIdentity.contour_limit_assembly
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-16T13:43:40.185705+00:00
-- url     : https://prove2.me/theorems/21eff3e3-8a10-4f9d-ba91-87b867694a74
-- title:
--   Algebraic assembly after contour limits
-- statement:
--   Once the limiting contour integrals have been identified, the two bank contributions combine into twice the normalized bank term and the inner and outer arc limits cancel. If the total boundary integral equals the residue contribution, then twice the bank term equals the same residue contribution.
-- source:
--   Internal contour-limit assembly lemma for the weighted-root keyhole proof.

import Mathlib

namespace WeightedRootIntegralIdentity

theorem contour_limit_assembly (Iupper Ilower Iinner Iouter residue Ibank : ℂ) (hbank : Iupper + Ilower = 2 * Ibank) (harcs : Iinner + Iouter = 0) (hboundary : Iupper + Ilower + Iinner + Iouter = 2 * Real.pi * Complex.I * residue) : 2 * Ibank = 2 * Real.pi * Complex.I * residue := by sorry

end WeightedRootIntegralIdentity
