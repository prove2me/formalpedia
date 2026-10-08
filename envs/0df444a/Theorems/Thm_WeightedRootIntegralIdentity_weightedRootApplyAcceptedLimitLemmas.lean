-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weightedRootApplyAcceptedLimitLemmas
-- name    : WeightedRootIntegralIdentity.weightedRootApplyAcceptedLimitLemmas
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-20T05:07:44.257882+00:00
-- url     : https://prove2.me/theorems/df084b27-0256-4f9e-8a5d-a63a14cc6147
-- title:
--   Apply the accepted contour limit lemmas
-- statement:
--   Suppose the finite contour equation has constant right-hand side residue. If the upper and lower banks converge to U and L, while the right and left vertical sides and inner and outer arcs vanish, then the limiting bank balance is U+L=residue.
-- source:
--   Termwise convergence of the finite contour equation, using the accepted vertical-side, bank, arc, and finite-to-limiting lemmas.

import Mathlib
open Filter Topology
namespace WeightedRootIntegralIdentity
theorem weightedRootApplyAcceptedLimitLemmas
    (Iu Il Vr Vl Ii Io : ℕ → ℂ) (U L residue : ℂ)
    (hu : Tendsto Iu atTop (𝓝 U))
    (hl : Tendsto Il atTop (𝓝 L))
    (hvr : Tendsto Vr atTop (𝓝 0))
    (hvl : Tendsto Vl atTop (𝓝 0))
    (hi : Tendsto Ii atTop (𝓝 0))
    (ho : Tendsto Io atTop (𝓝 0))
    (hfinite : ∀ m : ℕ,
      Iu m + Il m + Vr m + Vl m + Ii m + Io m = residue) :
    U + L = residue := by sorry
end WeightedRootIntegralIdentity
