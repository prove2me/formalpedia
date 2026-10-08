-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weightedRootConcreteResidueCauchyBalanceV3
-- name    : WeightedRootIntegralIdentity.weightedRootConcreteResidueCauchyBalanceV3
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-20T05:31:56.631999+00:00
-- url     : https://prove2.me/theorems/36e27696-8afc-464c-a5a8-0285618dd372
-- title:
--   Concrete weighted residue Cauchy balance
-- statement:
--   When the finite contour equation has the weighted residue term from the origin and reciprocal-infinity expansions, and the vertical sides and circular arcs vanish while the banks converge, the limiting bank sum equals the concrete weighted residue contribution.
-- source:
--   Apply the accepted limit lemmas to the finite contour equation and specialize its constant to the weighted residue expression.

import Mathlib
open Filter Topology
open scoped BigOperators Interval
namespace WeightedRootIntegralIdentity
theorem weightedRootConcreteResidueCauchyBalanceV3
    (n : ℕ) (a w : ℕ → ℝ) (Iu Il Vr Vl Ii Io : ℕ → ℂ) (U L : ℂ)
    (hu : Tendsto Iu atTop (𝓝 U))
    (hl : Tendsto Il atTop (𝓝 L))
    (hvr : Tendsto Vr atTop (𝓝 0))
    (hvl : Tendsto Vl atTop (𝓝 0))
    (hi : Tendsto Ii atTop (𝓝 0))
    (ho : Tendsto Io atTop (𝓝 0))
    (hfinite : ∀ m : ℕ,
      Iu m + Il m + Vr m + Vl m + Ii m + Io m =
        2 * Real.pi * Complex.I *
          (-(deriv (fun u : ℂ =>
            ∏ i ∈ Finset.range n, (1 - (a i : ℂ) * u) ^ (w i : ℂ)) 0).re +
            (∏ i ∈ Finset.range n,
              (((0 : ℂ) - (a i : ℂ)) ^ (w i : ℂ))).re)) :
    U + L = 2 * Real.pi * Complex.I *
      (-(deriv (fun u : ℂ =>
        ∏ i ∈ Finset.range n, (1 - (a i : ℂ) * u) ^ (w i : ℂ)) 0).re +
        (∏ i ∈ Finset.range n,
          (((0 : ℂ) - (a i : ℂ)) ^ (w i : ℂ))).re) := by sorry
end WeightedRootIntegralIdentity
